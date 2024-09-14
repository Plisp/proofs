datatype exp = Id of string | App of string * exp list;

datatype form = Prop of string * exp list
              | Bot
              | Conj of form * form
              | Disj of form * form
              | Imp of form * form
              | Exi of string * form
              | All of string * form
              | Eql of exp * exp
;

fun csv f [] = ""
  | csv f [v] = f v
  | csv f (v::vs) = f v ^ "," ^ csv f vs
;

fun dispe (Id v) = v
  | dispe (App (fv,es)) = fv ^ "(" ^ csv dispe es ^ ")"
;

local
    fun prec "c" "d" = true
      | prec "c" "i" = true
      | prec "d" "i" = true
      | prec _ _ = false

    fun wrap d c s = if prec d c then "(" ^ s ^ ")" else s
in
    fun disp _ (Prop (p,es)) = p ^ "(" ^ csv dispe es ^ ")"
      | disp _ Bot = "False"
      | disp _ (Conj (a,b)) = disp "c" a ^ " /\\ " ^ disp "c" b
      | disp d (Disj (a,b)) = wrap d "d" (disp "d" a ^ " \\/ " ^ disp "d" b)
      | disp d (Imp (a,b)) = wrap d "i" (disp "i" a ^ " -> " ^ disp "i" b)
      | disp _ (Exi (v,p)) = "(?" ^ v ^ ". " ^ disp "e" p ^ ")"
      | disp _ (All (v,p)) = "(!" ^ v ^ ". " ^ disp "a" p ^ ")"
      | disp _ (Eql (a,b)) = dispe a ^ " = " ^ dispe b
end;

print (disp " " (Disj (Exi ("a",Eql (App ("f",[Id "a"]), Id "c")),
                      (All ("a",Imp (Prop ("P",[Id "a", Id "c"]),
                                     Conj (Prop ("Q",[Id "a"]), Prop ("R",[])))))))
       ^ "\n");
