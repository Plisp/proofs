open HolKernel boolLib bossLib BasicProvers;
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

val _ = set_mapped_fixity
        {fixity = Infix(NONASSOC, 450), tok = "≈", term_name = "itree_wbisim"};

(* these are useful for bisimulation TODO how to do higher numbers? *)
val or1_tac = disj1_tac
val or2_tac = disj2_tac >> disj1_tac;
val or3_tac = disj2_tac >> disj2_tac;

(*/ basic examples of itree definition
   itree_unfold f is the final (coinductive) arrow to the capital algebra
   where f = structure map (into primed itree), seed = itree algebra instance
*)

Theorem spin_unfold:
  spin = Tau spin
Proof
  rw[spin, Once itree_unfold]
QED

(* echo taken from paper, a bit different with HOL unfold vs deptypes *)

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

(*/ basic rephrasings
   not sure whether this should be kept around but lemmas use it atm
*)

(* iiter (Ret INL) → Tau (itree_unfold (iiter_cb (mrec_cb h_prog))
                           (mrec_cb h_prog (⋆ (rh state_res) k))) to continue *)
(* mrec: Vis (INL (prog × newstate)) k → Ret (INL (h_prog prog ⋆ k)) *)
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

(* Dec cleanup *)
Definition revert_binding_def:
  revert_binding name old_s
  = (λ(res,s').
       Ret
       (res,
        s' with locals :=
        res_var s'.locals (name,FLOOKUP old_s.locals name)))
End

(*/ various abstract nonsense
   just to have a richer equational theory, unfold continuations suck to read
*)

(* TODO itree_wbisim_tau is overloaded! fix so I can use that instead *)
Theorem itree_wbisim_add_tau:
  ∀ t. Tau t ≈ t
Proof
  qspecl_then [‘λa b. a = Tau b’] strip_assume_tac itree_wbisim_strong_coind >>
  strip_tac >>
  pop_assum irule >>
  rw[] >>
  Cases_on ‘t'’ >> rw[] >>
  disj2_tac >>
  rw[itree_wbisim_refl]
QED

(* TODO this should be a theorem! *)
Theorem strip_tau_retvis_refl:
  ∀t. (∃e g. t = Vis e g) ∨ (∃r. t = Ret r) ⇒ strip_tau t t
Proof
  metis_tac[strip_tau_cases]
QED

(* TODO type variable error? *)
Theorem iterbind_lemma:
  ∀rh k. (∀a. ∃p s. (k a) = (Ret (p, s))) ⇒
         ∀t. (itree_iter (mrec_cb h_prog) (⋆ t k))
             ≈ (⋆ (itree_iter (mrec_cb h_prog) t) k)
Proof
  ?
QED

(* relies on mrec_cb h_prog rev -> only Ret INR, so can't prolong iteration *)
(* also applies to while and cond! *)
Theorem dec_lemma:
  ∀ t name s.
    itree_iter (mrec_cb h_prog) (⋆ t (revert_binding name s))
  ≈ ⋆ (itree_iter (mrec_cb h_prog) t) (revert_binding name s)
Proof
  qspecl_then
  [‘λa b. ∃t name s.
     a = (itree_iter (mrec_cb h_prog) (⋆ t (revert_binding name s))) ∧
     b = (⋆ (itree_iter (mrec_cb h_prog) t) (revert_binding name s))’]
              strip_assume_tac itree_wbisim_strong_coind >>
  rw[] >>
  pop_assum irule >>
  rw[] >> (* TODO does soemthing different interactively? *)
  Cases_on ‘t''’ >-
   (or3_tac >> (* Ret produces Ret, doesn't affect iter. easy! *)
    Cases_on ‘x’ >>
    rw[revert_binding_def] >>
    rw[Once itree_iter_thm, itree_bind_thm] >>
    rw[Once itree_iter_thm, itree_bind_thm]) >-
   (* Tau case is clear *)
   (or1_tac >>
    rw[Once itree_iter_thm, itree_bind_thm] >>
    rw[Once itree_iter_thm, itree_bind_thm] >>
    or1_tac >>
    metis_tac[]) >-
   (* Vis case is a bit tricky, depends on whether the event is silent *)
   (Cases_on ‘a’ >-
     (or1_tac >>
      rw[Once itree_iter_thm, itree_bind_thm] >>
      rw[Once itree_iter_thm, itree_bind_thm] >>
      or1_tac >>
      rw[GSYM itree_bind_assoc] >>
      metis_tac[]) >-
     (or2_tac >>
      rw[Once itree_iter_thm, itree_bind_thm] >>
      rw[Once itree_iter_thm, itree_bind_thm] >>
      or1_tac >>
      qexistsl_tac [‘Tau (g r)’, ‘name’, ‘s’] >>
      CONJ_TAC >-
       (CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV[itree_bind_thm] >>
        CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV[itree_iter_thm] >>
        rw[itree_bind_thm]) >-
       (CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV[itree_iter_thm] >>
        rw[itree_bind_thm]))) >>
  metis_tac[]
QED

Theorem dec_thm:
  (eval s e = SOME k) ⇒
  (itree_mrec h_prog (Dec name e p,s)) ≈
  (itree_bind
   (itree_mrec h_prog (p,s with locals := s.locals |+ (name,k)))
   (revert_binding name s))
Proof
  rw[itree_mrec_alt] >>
  rw[h_prog_def, h_prog_rule_dec_def] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  rw[GSYM revert_binding_def] >>
  metis_tac[dec_lemma, itree_wbisim_add_tau, itree_wbisim_trans]
QED

(*/ massaging into ffi itree
   this doesn't have a nice equational theory, but simps should do most of the work
 *)

Definition massage_cb_def[simp]:
    massage_cb (INL (Ret (res, s))) = Ret' res
  ∧ massage_cb (INR (Ret (res',s'))) = Ret' res'
  ∧ massage_cb (INL (Tau t)) = Tau' (INL t)
  ∧ massage_cb (INR (Tau t')) = Tau' (INR t')
  ∧ massage_cb (INL (Vis (e,k) g)) = Vis' e (λr. INR (k r))
  ∧ massage_cb (INR (Vis e' g')) = Vis' e' (INR ∘ g')
End

(* massage Ret type from (η x state) -> η *)
(* convert Vis (sem_vis_event x (FFI_result -> itree)) ((prog x state) -> %itree)
-> Vis sem_vis_event (FFI_result -> itree) *)
Definition massage_def:
  massage x = itree_unfold massage_cb (INL x)
End

(* TODO can the INR case be split out so Vis is nicer *)
Theorem massage_thm:
  massage (Ret (res, s)) = Ret res
  ∧ massage (Tau t) = Tau (massage t)
Proof
  rw[massage_def] >-
   rw[Once itree_unfold] >-
   (rw[Once itree_unfold] >> rw[GSYM massage_def])
QED

Theorem itree_evaluate_alt:
  itree_evaluate p s = massage (itree_mrec h_prog (p,s))
Proof
  rw[itree_evaluate_def, massage_def] >>
  AP_THM_TAC >> (* same fn => same on same arg, backwards *)
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE massage_cb_def]
QED

(*/ pancake programs
   & parsing utilities
*)

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

(* obligatory *)

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

(* TODO fix this and do while *)
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
}’;

Definition loop_sem_def:
  loop_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD $ THE ^loop_ast) s
End

(* TODO ask Gordon about this *)
Theorem cheat1:
  0w < 1w
Proof
  cheat
QED

Definition h_prog_whilebody_cb_def[simp]:
    h_prog_whilebody_cb p (SOME Break) s' = Ret (INR (NONE,s'))
  ∧ h_prog_whilebody_cb p (SOME Continue) s' = Ret (INL (p,s'))
  ∧ h_prog_whilebody_cb p NONE s' = Ret (INL (p,s'))
    (* nice! this syntax is valid *)
  ∧ h_prog_whilebody_cb p res s' = Ret (INR (res,s'))
End

Definition h_prog_while_cb_def[simp]:
    h_prog_while_cb seed p s NONE = Ret (INR (SOME Error,s))
  ∧ h_prog_while_cb seed p s (SOME (ValWord w))
    = (if (w ≠ 0w)
       then Vis (INL seed) (λ(res,s'). h_prog_whilebody_cb p res s')
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
  rw[DefnBase.one_line_ify NONE h_prog_whilebody_cb_def] >>
  rpt (PURE_TOP_CASE_TAC >> gvs[] >> rw[FUN_EQ_THM])
QED

Theorem loop_thm:
  loop_sem s = ARB
Proof
  rw[loop_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_dec_def] >>
  rw[eval_def] >>
  rw[Once itree_iter_alt] >>
  (* while comparision *)
  rw[Once h_prog_def, h_prog_rule_while_alt] >>
  rw[eval_def, word_cmp_def, FLOOKUP_UPDATE, cheat1] >>
  qmatch_goalsub_abbrev_tac ‘Vis (INL _) next_loop_cont’ >>
  (* wanna expand the inner one, the outer iter collapses itself *)
  rw[Once itree_iter_alt] >>
  rw[Once itree_iter_alt] >>
  (* first loop body assignment. Things are already wacky *)
  rw[h_prog_def, h_prog_rule_assign_def] >>
  rw[eval_def, FLOOKUP_UPDATE] >>
  rw[word_op_def, FLOOKUP_UPDATE, is_valid_value_def, shape_of_def] >>
  (* got * (Ret (NONE,s with locals := s.locals |+ («x»,ValWord 1w))) *)
  (* and some highly weird callback *)
  rw[itree_bind_def] >>
  qunabbrev_tac ‘next_loop_cont’ >>
  CONV_TAC $ LHS_CONV $ RAND_CONV $ RAND_CONV $ RAND_CONV $ RAND_CONV $ RAND_CONV $ PURE_ONCE_REWRITE_CONV[itree_unfold] >> rw[] >>
  rw[itree_unfold_iiter_Ret_INL, itree_unfold_ibind_INL_Tau] >>
  rw[itree_unfold_iiter_Vis_INL] >>
  CONV_TAC $ LHS_CONV $ RAND_CONV $ RAND_CONV $ RAND_CONV $ RAND_CONV $ RAND_CONV $ RAND_CONV $ PURE_ONCE_REWRITE_CONV[itree_unfold] >> rw[] >>
  (* expand iter and the problem becomes clear *)
  rw[Once itree_iter_alt] >>
  rw[itree_unfold_iiter_Ret_INL] >>
  (* h_prog running second assignment? where's the check *)
QED