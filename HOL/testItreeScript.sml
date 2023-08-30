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

(* utilities *)

Definition ibind_cb_def[simp]:
    ibind_cb k (INL (Ret r)) = itree_CASE (k r)
                                          (λs. Ret' s)
                                          (λt. Tau' (INR t))
                                          (λe g. Vis' e (INR ∘ g))
  ∧ ibind_cb k (INL (Tau t)) = Tau' (INL t)
  ∧ ibind_cb k (INL (Vis e g)) = Vis' e (INL ∘ g)
  ∧ ibind_cb k (INR (Ret r')) = Ret' r'
  ∧ ibind_cb k (INR (Tau t')) = Tau' (INR t')
  ∧ ibind_cb k (INR (Vis e' g')) = Vis' e' (INR ∘ g')
End

Theorem itree_bind_alt1:
  itree_bind t k = itree_unfold (ibind_cb k) (INL t)
Proof
  rw[itree_bind_def] >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE ibind_cb_def]
QED

(* manual unrolling hack to get the cb simp to fire *)
Theorem itree_bind_alt:
  itree_bind t k = case ibind_cb k (INL t) of
                     Ret' r => Ret r
                   | Tau' s => Tau (itree_unfold (ibind_cb k) s)
                   | Vis' e g => Vis e (itree_unfold (ibind_cb k) ∘ g)
Proof
  CONV_TAC $ LHS_CONV $ ONCE_REWRITE_CONV[itree_bind_alt1] >>
  rw[Once itree_unfold]
QED

(* won't loop because (ibind_cb (INR Ret)) only produces Ret *)
Theorem itree_unfold_ibind_INR_Ret:
  itree_unfold (ibind_cb k) (INR (Ret r)) = Ret r
Proof
  rw[Once itree_unfold]
QED

(* itree iter *)

Definition iiter_cb_def[simp]:
    iiter_cb body (Ret (INL cont)) = Tau' (body cont)
  ∧ iiter_cb body (Ret (INR r))    = Ret' r
  ∧ iiter_cb body (Tau t) = Tau' t
  ∧ iiter_cb body (Vis e g) = Vis' e g
End

Theorem itree_iter_alt1:
  itree_iter body seed = itree_unfold (iiter_cb body) (body seed)
Proof
  rw[itree_iter_def] >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE iiter_cb_def]
QED

Theorem itree_iter_alt:
  itree_iter body seed = case iiter_cb body (body seed) of
                           Ret' r => Ret r
                         | Tau' s => Tau (itree_unfold (iiter_cb body) s)
                         | Vis' e g => Vis e (itree_unfold (iiter_cb body) ∘ g)
Proof
  CONV_TAC $ LHS_CONV $ ONCE_REWRITE_CONV[itree_iter_alt1] >>
  rw[Once itree_unfold]
QED

Theorem itree_unfold_iiter_Ret_INL:
  itree_unfold (iiter_cb k) (Ret (INL r)) = Tau (itree_unfold (iiter_cb k) (k r))
Proof
  rw[Once itree_unfold]
QED

Theorem itree_unfold_iiter_Ret_INR:
  itree_unfold (iiter_cb k) (Ret (INR r)) = Ret r
Proof
  rw[Once itree_unfold]
QED

(* massage Ret type from (η x state) -> η *)
(* convert Vis (sem_vis_event x (FFI_result -> itree)) ((prog x state) -> %itree)
-> Vis sem_vis_event (FFI_result -> itree) *)

Definition massage_def[simp]:
    massage (INL (Ret (res, s))) = Ret' res
  ∧ massage (INR (Ret (res',s'))) = Ret' res'
  ∧ massage (INL (Tau t)) = Tau' (INL t)
  ∧ massage (INR (Tau t')) = Tau' (INR t')
  ∧ massage (INL (Vis (e,k) g)) = Vis' e (λr. INR (k r))
  ∧ massage (INR (Vis e'    g')) = Vis' e' (INR ∘ g')
End

Theorem itree_evaluate_alt:
  itree_evaluate p s = itree_unfold massage (INL (itree_mrec h_prog (p,s)))
Proof
  rw[itree_evaluate_def] >>
  AP_THM_TAC >> (* same fn => same on same arg, backwards *)
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE massage_def]
QED

Definition mrec_cb_def[simp]:
  mrec_cb rh (Ret r) = Ret (INR r) ∧
  mrec_cb rh (Tau t) = Ret (INL t) ∧
  mrec_cb rh (Vis (INL state_res) k) = Ret (INL (⋆ (rh state_res) k)) ∧
  mrec_cb rh (Vis (INR ffi_res) k) = Vis ffi_res (λx. Ret (INL (k x)))
End

Theorem itree_mrec_alt:
  itree_mrec rh seed = itree_iter (mrec_cb rh) (rh seed)
Proof
  rw[itree_mrec_def] >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE mrec_cb_def]
QED

(* Theorem itree_mrec_dec: *)
(*   itree_mrec ((Dec x exp prog),s) = *)
(*   case eval s exp of *)
(*     NONE => Ret(SOME Error) *)
(*   | SOME value => *)
(*       (Tau (itree_mrec prog (s with locals := s.locals |+ (x,value)))) *)
(* Proof *)
(*   rw[itree_semantics_def, itree_evaluate_alt] >> *)
(*   rw[Once itree_mrec_def, h_prog_def, h_prog_rule_dec_def] >> *)
(*   BasicProvers.PURE_TOP_CASE_TAC >> *)
(*   gvs[itree_iter_def] >- *)
(*    (rw[Once itree_unfold] >> *)
(*     rw[Once itree_unfold]) >> *)

(*   rw[Once itree_mrec_def] >> *)
(*   rw[itree_iter_def] >> *)

(*   unfold_inner >> rw[] >> *)
(*   CONV_TAC $ LHS_CONV $ SIMP_CONV std_ss[Once itree_unfold, massage_def] >> rw[] >> *)
(*   (* internal itree type doesn't match *) *)
(* QED *)

(* RAND_CONV : f x (unfold) -> x *)

Definition mrec_test_def:
  mrec_test (s:('a,'ffi) panSem$state)
  = itree_evaluate (Seq Skip (Return (Const 42w))) s
End

Theorem itree_mrec_test:
  mrec_test s = Tau (Tau (Ret (SOME (Return (ValWord 42w)))))
Proof
  rw[mrec_test_def, itree_evaluate_alt] >>
  rw[itree_mrec_alt, h_prog_def] >>
  rw[h_prog_rule_seq_def] >>
  rw[itree_iter_alt] >>
  rw[h_prog_def] >>
  rw[itree_bind_alt] >>
  rw[itree_trigger_def] >>
  (* return *)
  rw[h_prog_def,h_prog_rule_return_def,size_of_shape_def,shape_of_def,eval_def] >>
  rw[itree_bind_alt, itree_unfold_ibind_INR_Ret] >>
  rw[itree_unfold_iiter_Ret_INL] >>
  rw[itree_unfold_iiter_Ret_INR] >>
  rw[Once itree_unfold, massage_def] >>
  rw[Once itree_unfold, massage_def] >>
  rw[Once itree_unfold, massage_def]
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
