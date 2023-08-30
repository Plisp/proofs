open stringLib helperLib;
open finite_mapTheory; (* flookup_thm *)
open itreeTauTheory;

open asmTheory; (* word_cmp_def *)
open wordsTheory; (* n2w_def *)
open wordLangTheory; (* word_op_def *)
open panPtreeConversionTheory; (* parse_funs_to_ast *)
open panLangTheory; (* size_of_shape_def *)
open panSemTheory; (* eval_def *)
open panItreeSemTheory;

(* open bitstringTheory;*)

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

(* manual unrolling hack to get the cb simp to fire *)
Theorem itree_bind_alt1:
  itree_bind t k = itree_unfold (ibind_cb k) (INL t)
Proof
  rw[itree_bind_def] >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE ibind_cb_def]
QED

(* this is not safe as a simp due to the infinite Tau case *)
Theorem itree_bind_alt2:
  itree_unfold (ibind_cb k) (INL t) =
  case ibind_cb k (INL t) of
    Ret' r => Ret r
  | Tau' s => Tau (itree_unfold (ibind_cb k) s)
  | Vis' e g => Vis e (itree_unfold (ibind_cb k) ∘ g)
Proof
  rw[Once itree_unfold]
QED

Theorem itree_bind_alt:
  itree_bind t k = case ibind_cb k (INL t) of
                     Ret' r => Ret r
                   | Tau' s => Tau (itree_unfold (ibind_cb k) s)
                   | Vis' e g => Vis e (itree_unfold (ibind_cb k) ∘ g)
Proof
  rw[itree_bind_alt1, itree_bind_alt2]
QED

(* decreases depth of redexes, as the ibind_cb won't compute *)
Theorem itree_bind_Vis[simp]:
  itree_bind (Vis e g) k = Vis e (itree_unfold (ibind_cb k) ∘ (INL ∘ g))
Proof
  rw[itree_bind_alt]
QED

(* TODO when to use simps? it's like proving strong normalization?!*)
Theorem itree_unfold_ibind_INR_Ret[simp]:
  itree_unfold (ibind_cb k) (INR (Ret r)) = Ret r
Proof
  rw[Once itree_unfold]
QED

Theorem itree_unfold_ibind_INR_Vis[simp]:
  itree_unfold (ibind_cb k) (INR (Vis e g))
  = Vis e (itree_unfold (ibind_cb k) ∘ INR ∘ g)
Proof
  rw[Once itree_unfold]
QED

Theorem itree_unfold_ibind_INL_Vis[simp]:
  itree_unfold (ibind_cb k) (INL (Vis e g))
  = Vis e (itree_unfold (ibind_cb k) ∘ INL ∘ g)
Proof
  rw[Once itree_unfold]
QED

Theorem itree_unfold_ibind_INR_Tau:
  itree_unfold (ibind_cb k) (INR (Tau t)) = Tau (itree_unfold (ibind_cb k) (INR t))
Proof
  rw[Once itree_unfold]
QED

Theorem itree_unfold_ibind_INL_Tau:
  itree_unfold (ibind_cb k) (INL (Tau t)) =  Tau (itree_unfold (ibind_cb k) (INL t))
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

(* not a safe simp as kr may produce Ret (INL r') *)
Theorem itree_unfold_iiter_Ret_INL:
  itree_unfold (iiter_cb k) (Ret (INL r)) = Tau (itree_unfold (iiter_cb k) (k r))
Proof
  rw[Once itree_unfold]
QED

Theorem itree_unfold_iiter_Ret_INR[simp]:
  itree_unfold (iiter_cb k) (Ret (INR r)) = Ret r
Proof
  rw[Once itree_unfold]
QED

Theorem itree_unfold_iiter_Vis_INL:
  itree_unfold (iiter_cb k) (Vis e g) = Vis e (itree_unfold (iiter_cb k) ∘ g)
Proof
  rw[Once itree_unfold]
QED

(* massage Ret type from (η x state) -> η *)
(* convert Vis (sem_vis_event x (FFI_result -> itree)) ((prog x state) -> %itree)
-> Vis sem_vis_event (FFI_result -> itree) *)

Definition massage_cb_def[simp]:
    massage_cb (INL (Ret (res, s))) = Ret' res
  ∧ massage_cb (INR (Ret (res',s'))) = Ret' res'
  ∧ massage_cb (INL (Tau t)) = Tau' (INL t)
  ∧ massage_cb (INR (Tau t')) = Tau' (INR t')
  ∧ massage_cb (INL (Vis (e,k) g)) = Vis' e (λr. INR (k r))
  ∧ massage_cb (INR (Vis e' g')) = Vis' e' (INR ∘ g')
End

Definition massage_def:
  massage x = itree_unfold massage_cb (INL x)
End

Theorem itree_evaluate_alt:
  itree_evaluate p s = massage (itree_mrec h_prog (p,s))
Proof
  rw[itree_evaluate_def, massage_def] >>
  AP_THM_TAC >> (* same fn => same on same arg, backwards *)
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE massage_cb_def]
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
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_seq_def] >>
  (* Seq expanded, proceed with iter *)
  rw[itree_iter_alt] >>
  (* reduce the callback first *)
  rw[h_prog_def] >>
  rw[itree_trigger_def] >>
  (* execute skip and unfold further *)
  rw[Once itree_bind_alt] >> (* Once: another bind is produced from Vis INL *)
  rw[h_prog_def, h_prog_rule_return_def] >>
  rw[size_of_shape_def, shape_of_def, eval_def] >>
  (* execute return *)
  rw[itree_bind_alt] >>
  (* massage return type and expand *)
  rw[massage_def] >>
  rpt (rw[Once itree_unfold])
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

(* the obligatory, even though the earlier one was way more involved *)

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
  rw[hello_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_return_def] >>
  rw[eval_def, size_of_shape_def, shape_of_def] >>
  rw[itree_iter_alt] >>
  rw[massage_def] >>
  rw[Once itree_unfold]
QED

(* manual loop unrolling isn't too bad with rewrites *)

val loop_ast = rhs $ concl $ parse_pancake ‘
fun fn() {
  var x = 0;
  while (x < 1) {
      x = x + 1;
  }
  return x;
}’;

Definition loop_sem_def:
  loop_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD $ THE ^loop_ast) s
End

(* TODO extra parameter r? how to reshape case *)
Definition h_prog_whilebody_cb_def[simp]:
    h_prog_whilebody_cb p r (SOME Break) s' = Ret (INR (NONE,s'))
  ∧ h_prog_whilebody_cb p r (SOME Continue) s' = Ret (INL (p,s'))
  ∧ h_prog_whilebody_cb p r NONE s' = Ret (INL (p,s'))
    (* nice! this syntax is valid *)
  ∧ h_prog_whilebody_cb p r res s' = Ret (INR (r,s'))
End

Definition h_prog_while_cb_def[simp]:
    h_prog_while_cb seed p s NONE = Ret (INR (SOME Error,s))
  ∧ h_prog_while_cb seed p s (SOME (ValWord w))
    = (if (w ≠ 0w)
       then Vis (INL seed) (λ(res,s'). h_prog_whilebody_cb p res res s')
       else Ret (INR (NONE,s)))
  ∧ h_prog_while_cb seed p s (SOME (ValLabel _)) = Ret (INR (SOME Error,s))
  ∧ h_prog_while_cb seed p s (SOME (Struct _)) = Ret (INR (SOME Error,s))
End

Theorem h_prog_rule_while_alt:
  h_prog_rule_while g p s =
  itree_iter (λseed. (h_prog_while_cb seed p s (eval s g))) (p,s)
Proof
  rw[h_prog_rule_while_def] >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE h_prog_while_cb_def] >>
  rw[DefnBase.one_line_ify NONE h_prog_whilebody_cb_def]
QED

(* TODO *)
Theorem cheat1:
  0w < 1w
Proof
  cheat
QED

Theorem loop_thm:
  loop_sem s = ARB
Proof
  rw[loop_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_dec_def] >>
  rw[eval_def] >>
  rw[itree_iter_alt] >> (* TODO is Vis INL so internal bind works? *)
  (* seq *)
  rw[h_prog_def, h_prog_rule_seq_def] >>
  rw[itree_trigger_def] >> (* TODO indentation of ∘ composed functions *)
  (* while *)
  rw[h_prog_def, h_prog_rule_while_alt] >>
  rw[eval_def, word_cmp_def] >>
  rw[FLOOKUP_UPDATE, cheat1] >>

  rw[itree_iter_alt] >>
  rw[itree_unfold_iiter_Ret_INL] >>
  (* first loop body assignment. Note: conts for scope exit and return *)
  rw[h_prog_def, h_prog_rule_assign_def] >>
  rw[eval_def, FLOOKUP_UPDATE] >>
  rw[word_op_def, FLOOKUP_UPDATE, is_valid_value_def, shape_of_def] >>
  (* got * (Ret (NONE,s with locals := s.locals |+ («x»,ValWord 1w))) *)
  (* TODO lots of continuations *)
  rw[Once itree_bind_def] >>
  CONV_TAC $ LHS_CONV $ RAND_CONV $ RAND_CONV $ RAND_CONV $ RAND_CONV $ RAND_CONV $ PURE_ONCE_REWRITE_CONV[itree_unfold] >> rw[] >>
  (* TODO why doesn't qabbrev work *)
  rw[itree_unfold_iiter_Ret_INL] >>
  rw[itree_unfold_iiter_Vis_INL] >>
  rw[itree_unfold_ibind_INR_Tau] >>
  rw[itree_unfold_ibind_INL_Tau] >>
  rw[itree_unfold_iiter_Ret_INL] >>
  rw[itree_unfold_ibind_INR_Vis] >>
  rw[itree_unfold_ibind_INL_Vis] >>
QED
