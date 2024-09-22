(* utilities *)

fun inter s f [] = ""
  | inter s f [v] = f v
  | inter s f (v::vs) = f v ^ s ^ inter s f vs

fun csv f = inter "," f;

(* datatypes *)

datatype exp = Id of string | Sch of string | App of string * exp list

datatype form = Prop of string * exp list
              | Conj of form * form
              | Disj of form * form
              | Imp of form * form
              | Exi of string * form
              | All of string * form
              | Eql of exp * exp

fun dispe (Id v) = v
  | dispe (Sch v) = "?" ^ v
  | dispe (App(fv,es)) = fv ^ "(" ^ csv dispe es ^ ")"

local
    fun prec "c" "d" = true
      | prec "c" "i" = true
      | prec "d" "i" = true
      | prec _ _ = false

    fun wrap d c s = if prec d c then "(" ^ s ^ ")" else s
    fun disp' _ (Prop(p,es)) = p ^ "(" ^ csv dispe es ^ ")"
      | disp' _ (Conj(a,b)) = disp' "c" a ^ " /\\ " ^ disp' "c" b
      | disp' d (Disj(a,b)) = wrap d "d" (disp' "d" a ^ " \\/ " ^ disp' "d" b)
      | disp' d (Imp(a,b)) = wrap d "i" (disp' "i" a ^ " -> " ^ disp' "i" b)
      | disp' _ (Exi(v,p)) = "(?" ^ v ^ ". " ^ disp' "e" p ^ ")"
      | disp' _ (All(v,p)) = "(!" ^ v ^ ". " ^ disp' "a" p ^ ")"
      | disp' _ (Eql(a,b)) = dispe a ^ " = " ^ dispe b
in
val disp = disp' "";
end;

print(disp (Disj(Exi("a", Eql(App("f", [Id "a"]), Id "c")),
                (All("a", Imp(Prop("P", [Id "a", Id "c"]),
                              Conj(Prop("Q", [Id "a"]), Prop("R", [])))))))
      ^ "\n");

(* utilities for manipulating formulae *)

val vcount = ref 0;
type goalstate = { assms : form list , goal : form list }

fun freshen v = (vcount := !vcount + 1 ; Id (v ^ Int.toString(!vcount)))

local
    fun subste s t (Id id) = if s = id then t else Id id
      | subste s t (Sch id) = if s = id then t else Sch id
      | subste s t (App(f, es)) = App(f, map (fn e => subste s t e) es)
in
fun subst s t (Prop(p, es)) = Prop(p, map (fn e => subste s t e) es)
  | subst s t (Conj(a,b)) = Conj(subst s t a, subst s t b)
  | subst s t (Disj(a,b)) = Disj(subst s t a, subst s t b)
  | subst s t (Imp(a,b)) = Imp(subst s t a, subst s t b)
  | subst s t (Exi(v,p)) = if s = v then Exi(v,p) else Exi(v, subst s t p)
  | subst s t (All(v,p)) = if s = v then All(v,p) else All(v, subst s t p)
  | subst s t (Eql(a,b)) = Eql(subste s t a, subste s t b)
end;

fun asm_canon (Conj(a,b)) = asm_canon a @ asm_canon b
  | asm_canon (Exi(v,p)) = asm_canon(subst v (freshen v) p)
  | asm_canon p = [p]

fun canon (Conj(a,b)) = canon a @ canon b
  | canon (Imp(a,b)) = map (fn {assms, goal}
                               => {assms = asm_canon a @ assms, goal = goal})
                           (canon b)
  (* TODO unsound to split conj with schemas *)
  (* | canon (Exi(v,p)) = canon(subst v (freshen("?" ^ v)) p) *)
  | canon (All(v,p)) = canon(subst v (freshen v) p)
  | canon p = [{ assms = [] , goal = p }]

fun disp_goalst {assms, goal}
    = inter "\n" disp assms ^ "\n-------------------------\n" ^
      disp goal ^ "\n\n"

val print_goals = print o disp_goalst;

val example = (Imp (Conj (Prop ("P",[]),
                          Imp(Prop("P",[]), Prop("F",[]))),
                    Prop("F",[])));

val example_canon = map print_goals (canon example);

(* strategy:
 *  1. apply safe rules, except eliminating disjunctions
 *  2. try to unify schematics, but not with each other
 *  3. insert any solved conjuncts as assumptions for others
 *)

(* note: a schema will not unify with itself *)
fun noccurs v (Id _) = true
  | noccurs v (Sch v') = (v <> v')
  | noccurs v (App (f,es)) = List.all (noccurs v) es

fun unifye (Id v1) (Id v2) = if v1 = v2 then SOME [] else NONE
  | unifye (Sch v1) (Id v2) = SOME [(v1, Id v2)]
  | unifye (Id v1) (Sch v2) = SOME [(v2, Id v1)]
  | unifye (Sch v) app = if noccurs v app then SOME [(v, app)] else NONE
  | unifye app (Sch v) = unifye (Sch v) app
  | unifye (App(f1, e1s)) (App(f2, e2s))
    = if f1 = f2
      then let val res = map (fn (e1,e2) => unifye e1 e2) (ListPair.zip (e1s,e2s))
           in
               if List.all isSome res
               then SOME (foldl (fn (SOME s, substs) => s @ substs) [] res)
               else NONE
           end
      else NONE
  | unifye _ _ = NONE

local
    fun join (SOME l1) (SOME l2) = SOME (l1 @ l2)
      | join _ _ = NONE
in
fun unify (Prop(p1, e1s)) (Prop(p2, e2s)) = unifye (App (p1,e1s)) (App (p2,e2s))
  | unify (Conj(a1,b1)) (Conj(a2,b2)) = join (unify a1 a2) (unify b1 b2)
  | unify (Disj(a1,b1)) (Disj(a2,b2)) = join (unify a1 a2) (unify b1 b2)
  | unify (Imp(a1,b1)) (Imp(a2,b2)) = join (unify a1 a2) (unify b1 b2)
  | unify (Exi(v1,p1)) (Exi(v2,p2)) = unify p1 (subst v2 (Id v1) p2)
  | unify (All(v1,p1)) (All(v2,p2)) = unify p1 (subst v2 (Id v1) p2)
  | unify (Eql(a1,b1)) (Eql(a2,b2)) = join (unifye a1 a2) (unifye b1 b2)
  | unify _ _ = NONE
end;

(* no conjunction, except in schema case *)

fun solve {assms, goal = (Prop (p,es))}
    = List.exists
          (fn assm =>
              let fun try cand new = (let val res = unify cand (Prop (p,es))
                                      in if isSome res
                                         then solve new
                                         else false
                                      end)
              in (case assm of
                      Prop (p',es')
                      => if isSome (unify (Prop (p',es')) (Prop (p,es)))
                        then (print ("solved: " ^ disp (Prop (p,es)) ^ "\n") ; true)
                        else false
                    | Imp (m,c) => false
                    | _ => false)
              end)
          assms
  | solve {assms, goal = (Disj (a,b))}
    = false
      (* let val res = prove (canon a) *)
      (*     val combined = {assms = assms @ assms', goal = goal'} *)
      (* in *)
      (*     if res *)
      (*     then (print "solved " ^ disp goal'; true) *)
      (*     else let val {assms' , goal'} = canon b *)
      (*              val combined = {assms = assms @ assms', goal = goal'} *)
      (*          in if solve combined *)
      (*             then (print "solved " ^ disp goal'; true) *)
      (*             else false *)
      (*          end *)
      (* end *)
  | solve {assms, goal = (Exi (v,p))} = false
  | solve _ = false
and prove form = map solve (map print_goals (canon form) ; (canon form))

val _ = prove (Imp (Prop ("P", []),Prop ("P", [])));
