fun the NONE = raise Fail "THE failed"
  | the (SOME m) = m;

(*
 * tree predicate calculator
 *)
type 'a obj = int -> 'a;
type psub = int;
type 'a pred = ('a -> psub) obj;

val top : int obj = fn i => i;
val bot : int obj = fn i => 0;
fun land ca cb = fn i => Int.min (ca i, cb i);
fun lor ca cb = fn i => Int.max (ca i, cb i);
fun later c = fn i => Int.min (i, c i + 1);
fun limp ca cb = fn i => if ca i <= cb i then i else cb i;

fun eq (s : ''a obj) t : psub obj
    = fn i =>
         let fun test j = if s j <> t j then j-1
                          else if j = i then i
                          else test (j+1)
         in test 1 end;

fun lift (s : psub option obj) : psub obj
    = fn i => case s i of
                NONE => 1
              | SOME k => k + 1;

fun unfold (seed : 'a) (f : 'a -> 'b * 'a) =
    let fun unfold' i seed
            = if i = 0 then []
              else case f seed of (n,newSeed) => n :: unfold' (i - 1) newSeed
    in fn i => unfold' i seed end;

fun take n (a : 'a obj) : 'a list
    = if n = 0 then [] else take (n - 1) a @ [a n];

fun next (a : 'a obj) : ('a option) obj
    = fn i => if i = 1 then NONE else SOME (a (i - 1));

fun lapp (f : ('a -> 'b) option obj) (a : 'a option obj) : 'b option obj
    = fn i => case f i of
                NONE => NONE
              | SOME realF => SOME (realF (the (a i)));

(* morphisms from int->a to int->b are int->(a->b)
 * we need a restriction map to correctly simulate earlier stages of an object
 *)
fun toObj (rest : ('a * int) -> 'a) (f : 'a obj -> 'b obj) : ('a -> 'b) obj
    = fn i => fn a => f (fn j => if j <= i then rest (a,j)
                           else raise Fail "non causal")
                    i;

fun toFn (objF : ('a -> 'b) obj) : 'a obj -> 'b obj
    = fn objA => fn i => objF i (objA i);

(* calculate a guarded fixed-point *)
fun fix (func : 'a option obj -> 'a obj) : 'a obj
    = let fun fixpoint' i =
              if i = 1
              then func (fn _ => NONE) 1
              else func (fn i => SOME (fixpoint' (i - 1))) i
      in fixpoint' end;

(*
 * streams
 *)
type pstr = int list;

fun lhd (s : pstr obj) : int obj = fn i => hd (s i);

fun ltl (s : pstr obj) : pstr option obj
    = fn i => if i = 1 then NONE else SOME (tl (s i));

fun lhdSat (s : pstr obj) (P : int -> bool) : psub obj
    = if P (hd (s 1)) then top else bot;

val toStrPred : (pstr obj -> psub obj) -> (pstr -> psub) obj = toObj List.take;

(*
 * examples
 *)

val alternating = unfold 0 (fn i => (i mod 2, i+1));
fun const n = unfold 0 (fn s => (n, s));
fun ascending from by = unfold from (fn i => (i, i+by));

(* strict positive test *)
val onlyEvens = fix (fn recf =>
                        toStrPred (fn str => land (lhdSat str (fn n => n mod 2 = 0))
                                                (lift (lapp recf (ltl str)))));
val s1 = ascending 0 2;
val d1 = take 5 s1;
val p1 = take 5 (toFn onlyEvens s1);

val onlyZerod = fix (fn recf =>
                        toStrPred (fn str => land (eq (lhd str) bot)
                                                (lift (lapp recf (ltl str)))));
val s2 = unfold 0 (fn n => if n >= 3 then (1,0) else (0,n+1));
val d2 = take 5 s2;
val p2 = take 5 (toFn onlyZerod s2);

(* later r(tl s) => hd s = 0
 * trivial since 'classical'
 *)
val startsWithZero : (pstr -> psub) obj =
    fix (fn recf => toStrPred (fn str =>
                                limp (lift (lapp recf (ltl str)))
                                     (eq (lhd str) bot)));

(* later (r (tl s)) => later hd s >= hd (tl s)
 * also trivial, since the consequent predicate is 'classical'
 *)
val firstGeqSecond : (pstr -> psub) obj =
    fix (fn recf => toStrPred (fn str =>
                                limp (lift (lapp recf (ltl str)))
                                     (fn i => if i = 1 then 1
                                            else if hd (str i) >= hd (tl (str i))
                                            then i else 0)));

(* later (r (tl s)) => hd s = 0 /\ hd (tl s) = 0
 * ?
 *)
val firstSecondZero : (pstr -> psub) obj =
    fix (fn recf => toStrPred (fn str =>
                                limp (lift (lapp recf (ltl str)))
                                     (land (eq (lhd str) bot)
                                           (fn i => if i = 1 then 1
                                                  else if hd (tl (str i)) = 1
                                                  then i else 1))));

(* later (r (tl s)) => s = 0*
 * an alternation sequence
 *)
val oddZeroPrefix : (pstr -> psub) obj =
    fix (fn recf => toStrPred (fn str =>
                                limp (lift (lapp recf (ltl str)))
                                     (eq str (const 0))));

(* tree drawing *)
val horLine = "\226\149\180";
val teeRight = "\226\148\156";
val vertLine = "\226\148\130";
val downRight = "\226\149\176";
val upLeft = "\226\148\140";
fun printTree alphabet P maxDepth =
    let val last = List.last alphabet
        fun allTrue pstr =
            let val depth = List.length pstr
            in
                if List.length pstr >= maxDepth then true
                else List.all (fn t => t)
                              (map (fn c => if P (depth + 1) (pstr @ [c]) = depth+1
                                          then allTrue (pstr @ [c])
                                          else false)
                                   alphabet)
            end
        fun drawSub pstr =
            let val depth = List.length pstr
                fun pad last [] = ""
                  | pad last (i :: is) =
                    (if i <> last then vertLine ^ " " else "  ") ^ pad last is;
            in
                if depth >= maxDepth then ()
                else if not (allTrue pstr)
                then (map (fn c =>
                              (print ((if c = hd alphabet then horLine
                                       else "\n" ^ pad last pstr ^
                                            (if c <> last then teeRight
                                             else downRight) ^
                                            horLine)
                                      ^ Int.toString c)
                              ; if P (depth + 1) (pstr @ [c]) = depth+1 (* true *)
                                then drawSub (pstr @ [c])
                                else print "F"))
                          alphabet ; ())
                else if depth > 0
                then print "T"
                else ()
            end
    in print upLeft ; drawSub [] ; print "\n"
    end;
