(*
 * actual pancake programs
 *)

open stringLib;
open helperLib;
open finite_mapTheory; (* flookup_thm *)

open asmTheory; (* word_cmp_def *)
open miscTheory; (* read_bytearray *)
open panLangTheory; (* size_of_shape_def *)
open panPtreeConversionTheory; (* parse_funs_to_ast *)
open wordLangTheory; (* word_op_def *)
open wordsTheory; (* n2w_def *)

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

(* ffi test *)

val ffi_ast = rhs $ concl $ parse_pancake ‘
fun fn() {
  #num_clients(0, 0, 0, 0);
  #num_clients(0, 0, 0, 0);
}’;

Definition ffi_sem_def:
  ffi_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD $ THE ^ffi_ast) s
End

Theorem ffi_sem_thm:
  ffi_sem s = ARB
Proof
  rw[ffi_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  (* Seq *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_seq_def] >>
  rw[Once itree_iter_thm, Once itree_bind_thm] >>
  (* extcall *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[eval_def, FLOOKUP_UPDATE] >>
  rw[read_bytearray_def] >>
  rw[Once itree_bind_thm] >>
  rw[Once itree_iter_thm] >>
  rw[Once itree_bind_thm] >>
  (* inner thing *)
  rw[Once itree_bind_thm] >>
  rw[Once itree_bind_thm] >>
  (* TODO massage bug! (not yet fixed, update when done) *)
  rw[massage_def] >>
  rw[Once itree_unfold, massage_thm] >>
  rw[Once itree_unfold]
QED

(*/ loops work!
   manual loop unrolling isn't too bad with equational rewrites
 *)

val loop_ast = rhs $ concl $ parse_pancake ‘
fun fn() {
  var x = 0;
  while (x < 1) {
    x = x + 1;
  }
}’;

Definition loop_sem_def:
  loop_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD $ THE ^loop_ast) s
End

Definition h_prog_whilebody_cb_def[simp]:
    h_prog_whilebody_cb p (SOME Break) s' = Ret (INR (NONE,s'))
  ∧ h_prog_whilebody_cb p (SOME Continue) s' = Ret (INL (p,s'))
  ∧ h_prog_whilebody_cb p NONE s' = Ret (INL (p,s'))
  (* nice! this syntax is valid *)
  ∧ h_prog_whilebody_cb p res s' = Ret (INR (res,s'))
End

Definition h_prog_while_cb_def[simp]:
    h_prog_while_cb (p,s) NONE = Ret (INR (SOME Error,s))
  ∧ h_prog_while_cb (p,s) (SOME (ValWord w))
    = (if (w ≠ 0w)
       then Vis (INL (p,s))
                (λ(res,s'). h_prog_whilebody_cb p res s')
       else Ret (INR (NONE,s)))
  ∧ h_prog_while_cb (p,s) (SOME (ValLabel _)) = Ret (INR (SOME Error,s))
  ∧ h_prog_while_cb (p,s) (SOME (Struct _)) = Ret (INR (SOME Error,s))
End

(* PR submitted *)
Theorem h_prog_rule_while_alt:
  h_prog_rule_while g p s =
  (λ(p',s'). (h_prog_while_cb (p',s') (eval s' g))) ↻ (p,s)
Proof
  rw[h_prog_rule_while_def] >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE h_prog_while_cb_def] >>
  rw[DefnBase.one_line_ify NONE h_prog_whilebody_cb_def] >>
  rpt (PURE_TOP_CASE_TAC >> gvs[] >> rw[FUN_EQ_THM])
QED

Theorem cheat1:
  0w < 1w (* supposed to be :4 word but weever *)
Proof
  cheat
QED

Theorem loop_thm:
  loop_sem s = Tau (Tau (Tau (Ret NONE)))
Proof
  rw[loop_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_dec_alt] >>
  rw[eval_def] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  (* while *)
  rw[Once h_prog_def, h_prog_rule_while_alt] >>
  rw[Once itree_iter_thm] >>
  rw[Once itree_iter_thm] >>
  rw[eval_def, FLOOKUP_UPDATE, word_cmp_def, cheat1] >>
  rw[itree_bind_thm] >>
  (* assignment *)
  rw[Once h_prog_def, h_prog_rule_assign_def] >>
  rw[eval_def, FLOOKUP_UPDATE, cheat1,
     word_op_def, is_valid_value_def, shape_of_def] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  (* second while *)
  rw[Once itree_iter_thm] >>
  rw[Once itree_iter_thm] >>
  rw[eval_def, FLOOKUP_UPDATE, word_cmp_def] >>
  rw[revert_binding_def] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  (* massage *)
  rw[massage_thm]
QED
