open stringLib helperLib;
open finite_mapTheory; (* flookup_thm *)

open itreeTauTheory;
open panPtreeConversionTheory;
open panLangTheory; (* size_of_shape_def *)
open panSemTheory; (* eval_def *)
open panItreeSemTheory;

(* itree_unfold thm is the final (coinductive) arrow to Ret/Tau/Vis algebra *)

Theorem spin_unfold:
  spin = Tau spin
Proof
  rw[spin, Once itree_unfold]
QED

(* echo example *)

Datatype:
  IO = Input | Output num
End

Definition echo:
  echo = itree_unfold (λ s. case s of
                            | Input    => Vis' Input      (λ n. Output n)
                            | Output n => Vis' (Output n) (λ v. Input))
                      Input
End

Theorem echo_unfold:
  echo = Vis Input (λ n. Vis (Output n) (λ x. echo))
Proof
  rw[echo,       Once itree_unfold] >>
  rw[FUN_EQ_THM, Once itree_unfold]
QED

(* pancake programs *)

local
  val f =
    List.mapPartial
       (fn s => case remove_whitespace s of "" => NONE | x => SOME x) o
    String.tokens (fn c => c = #"\n")
in
  fun quote_to_strings q =
    f (Portable.quote_to_string (fn _ => raise General.Bind) q)
  end

fun parse_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “parse_funs_to_ast ^code”
end

val hello_ast = rhs $ concl $ parse_pancake ‘
fun fn() {
  return 42;
}’;

Definition hello_sem_def:
  hello_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate
  (SND $ SND $ HD $ THE ^hello_ast)
  s
End

Theorem hello_thm:
  hello_sem s = Ret (SOME (Return (ValWord 42w)))
Proof
  rw[hello_sem_def, itree_semantics_def, itree_evaluate_def] >>
  rw[Once itree_mrec_def, h_prog_def, h_prog_rule_return_def] >>
  rw[eval_def, size_of_shape_def, shape_of_def] >>
  rw[Once itree_iter_def] >>
  rw[Once itree_unfold] >>
  rw[Once itree_unfold]
QED

(* itree_iter *)
val loop_ast = rhs $ concl $ parse_pancake ‘
fun fn() {
  var x = 1;
  while (x < 3) {
      x = x + 1;
  }
  return x;
}’;

Definition loop_sem_def:
  loop_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD $ THE ^loop_ast) s
End

Theorem loop_thm:
  loop_sem s = ARB
Proof
  rw[loop_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  rw[Once itree_mrec_def, h_prog_def, h_prog_rule_dec_def] >>
  rw[eval_def] >>
  rw[itree_iter_def] >>
  rw[h_prog_def, h_prog_rule_seq_def] >>
  (*qmatch_goalsub_abbrev_tac ‘INL(itree_unfold a1 a2)’ >>
  qunabbrev_tac ‘a1’*)

  CONV_TAC $ LHS_CONV $ RAND_CONV $ PURE_ONCE_REWRITE_CONV [itree_unfold] >>
  rw[] >>
  rw[Once itree_unfold] >>
  rw[itree_bind_thm] >>
  your_face >>
  rw[] >>
  rw[h_prog_def, h_prog_rule_seq_def] >>
  rw[h_prog_rule_while_def] >>
  rw[itree_bind_def] >>
  PURE_ONCE_REWRITE_TAC [itree_unfold] >>
  cheat
QED
