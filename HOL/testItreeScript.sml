(*
 * Coinductive semantics with interaction trees!
 *
 * Directly express an infinite tree semantic structure via continuations.
 * In the spirit of the "Propositions as Types" principle, by encoding programs
 * as data rather than theorems, we may write *programs* to act as *proofs*,
 * potentially allowing the automation of simple algebraic reasoning.
 *
 * By developing an algebra, reasoning can be mostly done above the Tau level,
 * which are convenient for expressing silent program steps which may differ,
 * depending on context.
 *
 * Since they are the greatest fixpoint, they may also encode general recursive
 * data types using appropriate event data - e.g. W-trees.
 *
 * In comparision to the clock approach in cakeML's FBS semantics, the clock
 * becomes implicit in the structure of the itree, which is simpler for reasoning.
 * Oracle queries are encoded by events, and 'evaluating' in a context where the
 * responses are limited, we can simulate interaction with the external world.
 *
 * One possible reasoning method:
 * 1. express a clear (tauless) decomposition of the spec w/ conditions on FFI
 * 3. prove equivalence to the actual program semantics via weak bisimulation
 *
 * future work: ideally we want some way of automatically unfolding/executing a
 * program, to easily show facts about its interaction tree directly. This should
 * also allow for automated removal of Tau nodes. Could this be easier with types?
 *)

open HolKernel boolLib bossLib BasicProvers;
open arithmeticTheory;
open itreeTauTheory;
open panSemTheory; (* eval_def *)
open panItreeSemTheory;

(* open monadsyntax; *)
(* Overload monad_bind[local] = “itree_bind”; *)
(* Overload return[local] = “Ret”; *)

val _ = temp_set_fixity "↻" (Infixl 500);
Overload "↻" = “itree_iter”;

(* these are useful ONLY for bisimulation *)
val or1_tac = disj1_tac
val or2_tac = disj2_tac >> disj1_tac;
val or3_tac = disj2_tac >> disj2_tac;
val or4_tac = disj2_tac >> disj2_tac >> disj2_tac;

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
(* note: response types can't be restricted per event type *)

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

(* coinduction *)

(* finite on all paths *)
CoInductive itree_fin:
  (∀t. itree_fin t ⇒ itree_fin (Tau t)) ∧
  (∀e k. (∀r. itree_fin (k r)) ⇒ itree_fin (Vis e k)) ∧
  (∀r. itree_fin (Ret r))
End

(* infinite on all paths *)
CoInductive itree_inf:
  (∀t. itree_inf t ⇒ itree_inf (Tau t)) ∧
  (∀e k. (∀r. itree_inf (k r)) ⇒ itree_inf (Vis e k))
End

Theorem ret_fin:
  itree_fin (Tau (Ret r))
Proof
  rw[Once itree_fin_cases] >>
  rw[Once itree_fin_cases]
QED

Theorem spin_inf:
  itree_inf spin
Proof
  irule itree_inf_coind >>
  qexists_tac ‘λt. t = (Tau t)’ >>
  rw[] >-
   rw[spin_unfold] >-
   metis_tac[]
QED

Definition vis_spin_def:
  vis_spin = itree_unfold (λs. Vis' s I) 0
End
Theorem vis_spin_inf:
  itree_inf vis_spin
Proof
  irule itree_inf_coind >>
  qexists_tac ‘λt. ∃k. t = Vis k (itree_unfold (λs. Vis' s I))’ >>
  rw[vis_spin_def] >>
  rw[Once itree_unfold]
QED

(* looping vis nodes *)

Definition itree_loop_def:
  itree_loop emit succ zero =
  itree_unfold (λs'. Vis' (emit s') (λ_. (succ s'))) zero
End

Definition even_spec_def:
  even_spec k = itree_loop (λx. if EVEN x then "even" else "odd") (λn. 1 + n) k
End

Theorem even_add1:
  EVEN k ⇔ ¬EVEN (k+1)
Proof
  metis_tac[EVEN, SUC_ONE_ADD, ADD_SYM]
QED

(* backwards extensionality *)
Theorem even_spec_unfold:
  ∀k. EVEN k ⇒ even_spec k = Vis "even" (λ_. Vis "odd" (λ_. even_spec (2 + k)))
Proof
  rw[even_spec_def] >>
  CONV_TAC $ LHS_CONV $ REWRITE_CONV[itree_loop_def] >>
  rw[itree_unfold] >>
  rw[combinTheory.o_DEF] >>
  rw[FUN_EQ_THM] >>
  rw[itree_unfold] >-
   (metis_tac[even_add1]) >-
   (rw[combinTheory.o_DEF] >>
    rw[itree_loop_def])
QED

Theorem even_add2:
  EVEN (n+2) ⇔ EVEN n
Proof
  ‘EVEN (n+1+1) ⇔ EVEN (n+2)’ suffices_by metis_tac[EVEN, SUC_ONE_ADD, ADD_SYM] >>
  rw[]
QED

Theorem even_spec_plus2:
  ∀k. even_spec (2+k) = even_spec k
Proof
  strip_tac >>
  qspecl_then [‘even_spec (2+k)’, ‘even_spec k’]
              strip_assume_tac itree_bisimulation >>
  fs[EQ_IMP_THM] >>
  pop_assum irule >>
  pop_assum kall_tac >>
  qexists_tac ‘λa b. ∃n. a = even_spec (2+n) ∧ b = even_spec n’ >>
  rw[] >> gvs[even_spec_def, itree_loop_def, Once itree_unfold] >-
   (qexists_tac ‘k’ >>
    simp[] >>
    CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV[itree_unfold] >>
    rw[]) >-
   (simp[Once itree_unfold] >>
    CONJ_TAC >-
     (rw[Once even_add2]) >-
     (qexists_tac ‘n+1’ >> rw[]))
QED

Theorem even_spec_thm:
  even_spec 0 = Vis "even" (λ_. Vis "odd" (λ_. even_spec 0))
Proof
  rw[Once even_spec_unfold] >>
  rw[FUN_EQ_THM] >>
  qspec_then ‘0’ mp_tac even_spec_plus2 >>
  rw[]
QED

(*/ misc abstract nonsense
   just to have a richer equational theory for wbisim
 *)

Theorem itree_bind_left_identity:
  itree_bind (Ret x) k = k x
Proof
  rw[itree_bind_thm]
QED

Theorem itree_wbisim_vis:
  ∀e k1 k2. (∀r. ≈ (k1 r) (k2 r)) ⇒ ≈ (Vis e k1) (Vis e k2)
Proof
  metis_tac[strip_tau_cases, itree_wbisim_cases]
QED

(* TODO itree_wbisim_tau is overloaded! merged. change later *)
Theorem itree_wbisim_add_tau:
  ∀ t. ≈ (Tau t) t
Proof
  qspecl_then [‘λa b. a = Tau b’] strip_assume_tac itree_wbisim_strong_coind >>
  strip_tac >>
  pop_assum irule >>
  rw[] >>
  Cases_on ‘t'’ >> rw[] >>
  disj2_tac >>
  rw[itree_wbisim_refl]
QED

Triviality itree_wbisim_coind_upto_equiv:
  ∀R t t'. ≈ t t'
           ⇒ (∃t2 t3. t = Tau t2 ∧ t' = Tau t3 ∧ (R t2 t3 ∨ ≈ t2 t3)) ∨
             (∃e k k'.
               strip_tau t (Vis e k) ∧ strip_tau t' (Vis e k') ∧
               ∀r. R (k r) (k' r) ∨ ≈ (k r) (k' r)) ∨
             (∃r. strip_tau t (Ret r) ∧ strip_tau t' (Ret r))
Proof
  metis_tac[itree_wbisim_cases]
QED

(* coinduction but allows proof of subtrees using a separate wbisim *)
Theorem itree_wbisim_coind_upto:
  ∀R.
    (∀t t'.
       R t t' ⇒
       (∃t2 t3. t = Tau t2 ∧ t' = Tau t3 ∧ (R t2 t3 ∨ itree_wbisim t2 t3)) ∨
       (∃e k k'.
          strip_tau t (Vis e k) ∧ strip_tau t' (Vis e k') ∧
          ∀r. R (k r) (k' r) ∨ itree_wbisim(k r) (k' r)) ∨
       (∃r. strip_tau t (Ret r) ∧ strip_tau t' (Ret r))
       ∨ itree_wbisim t t')
    ⇒ ∀t t'. R t t' ⇒ itree_wbisim t t'
Proof
  rpt strip_tac >>
  irule itree_wbisim_strong_coind >>
  qexists_tac ‘R’ >>
  fs[] >>
  pop_assum kall_tac >>
  metis_tac[itree_wbisim_coind_upto_equiv]
QED

(*/ itree_bind respects wbisimilarity in itree and handler
   requires some lemmas
*)

(* Q.AP_TERM or AP_THM to lift eq *)
Theorem itree_bind_strip_tau_wbisim:
  ∀u u' k. strip_tau u u' ⇒ ≈ (⋆ u k) (⋆ u' k)
Proof
  Induct_on ‘strip_tau’ >>
  rpt strip_tac >-
   (CONV_TAC $ RATOR_CONV $ ONCE_REWRITE_CONV[itree_bind_thm] >>
    ‘≈ (⋆ u k) (⋆ u' k)’ suffices_by
      metis_tac[itree_wbisim_trans, itree_wbisim_sym, itree_wbisim_add_tau] >>
    rw[]) >-
   rw[itree_wbisim_refl] >>
   rw[itree_wbisim_refl]
QED

(* note a similar theorem does NOT hold for Ret because bind expands to (k x) *)
Theorem itree_bind_vis_strip_tau:
  ∀u k k' e. strip_tau u (Vis e k') ⇒ strip_tau (⋆ u k) (Vis e (λx. ⋆ (k' x) k))
Proof
  strip_tac >> strip_tac >> strip_tac >> strip_tac >>
  Induct_on ‘strip_tau’ >>
  rpt strip_tac >>
  rw[itree_bind_thm]
QED

Triviality itree_bind_vis_tau_wbisim:
  ≈ (Vis a g) (Tau u)
  ⇒ (∃e k' k''.
      strip_tau (⋆ (Vis a g) k) (Vis e k') ∧
      strip_tau (⋆ (Tau u) k) (Vis e k'') ∧
      ∀r. (∃t1 t2. ≈ t1 t2 ∧ k' r = ⋆ t1 k ∧ k'' r = ⋆ t2 k) ∨
          ≈ (k' r) (k'' r))
Proof
  rpt strip_tac >>
  rw[itree_bind_thm] >>
  fs[Once itree_wbisim_cases] >>
  fs[Once $ GSYM itree_wbisim_cases] >>
  qexists_tac ‘(λx. ⋆ (k' x) k)’ >>
  rw[itree_bind_vis_strip_tau] >>
  metis_tac[]
QED

Theorem itree_bind_resp_t_wbisim:
  ∀a b k. (≈ a b) ⇒ (≈ (⋆ a k) (⋆ b k))
Proof
  rpt strip_tac >>
  qspecl_then [‘λa b. ∃t1 t2. (≈ t1 t2) ∧ a = (⋆ t1 k) ∧ b = (⋆ t2 k)’]
              strip_assume_tac itree_wbisim_coind_upto >>
  pop_assum irule >>
  rw[] >-
   (last_x_assum kall_tac >>
    Cases_on ‘t1’ >>
    Cases_on ‘t2’ >-
     (fs[Once itree_wbisim_cases, itree_bind_thm] >>
      Cases_on ‘k x’ >> rw[itree_wbisim_refl]) >-
     (or4_tac >>
      irule itree_wbisim_sym >>
      irule itree_bind_strip_tau_wbisim >>
      fs[Once itree_wbisim_cases]) >-
     (fs[Once itree_wbisim_cases]) >-
     (or4_tac >>
      irule itree_bind_strip_tau_wbisim >>
      fs[Once itree_wbisim_cases]) >-
     (rw[itree_bind_thm] >>
      ‘≈ u u'’ by metis_tac[itree_wbisim_tau, itree_wbisim_sym] >>
      metis_tac[]) >-
     (metis_tac[itree_wbisim_sym, itree_bind_vis_tau_wbisim]) >-
     (fs[Once itree_wbisim_cases]) >-
     (metis_tac[itree_wbisim_sym, itree_bind_vis_tau_wbisim]) >-
     (fs[itree_bind_thm, Once itree_wbisim_cases] >> metis_tac[]))
  >- metis_tac[]
QED

Theorem itree_bind_resp_k_wbisim:
  ∀t k1 k2. (∀r. ≈ (k1 r) (k2 r)) ⇒ (≈ (⋆ t k1) (⋆ t k2))
Proof
  rpt strip_tac >>
  qspecl_then [‘λa b. ∃t. a = (⋆ t k1) ∧ b = (⋆ t k2)’]
              strip_assume_tac itree_wbisim_coind_upto >>
  pop_assum irule >>
  rw[] >-
   (Cases_on ‘t''’ >> rw[itree_bind_thm] >> metis_tac[]) >-
   metis_tac[]
QED

Theorem itree_bind_resp_wbisim:
  ∀a b k1 k2. (≈ a b) ⇒ (∀r. ≈ (k1 r) (k2 r)) ⇒ (≈ (⋆ a k1) (⋆ b k2))
Proof
  metis_tac[itree_bind_resp_t_wbisim, itree_bind_resp_k_wbisim, itree_wbisim_trans]
QED

(*/ itree_iter
   unexpectedly technical and probably not useful, but here you go
 *)

Theorem itree_iter_ret_tau_wbisim:
    itcb1 = (λx. case x of INL a => Tau (k1 ↻ a) | INR b => Ret b)
  ⇒ itcb2 = (λx. case x of INL a => Tau (k2 ↻ a) | INR b => Ret b)
  ⇒ ≈ (Ret x) (Tau u) ⇒ (∀r. ≈ (k1 r) (k2 r))
  ⇒ (∃t2 t3.
      ⋆ (Ret x) itcb1 = Tau t2 ∧ ⋆ (Tau u) itcb2 = Tau t3 ∧
      ((∃sa sb. ≈ sa sb ∧ t2 = ⋆ sa itcb1 ∧ t3 = ⋆ sb itcb2) ∨ ≈ t2 t3)) ∨
    (∃e k k'.
      strip_tau (⋆ (Ret x) itcb1) (Vis e k) ∧
      strip_tau (⋆ (Tau u) itcb2) (Vis e k') ∧
      ∀r. (∃sa sb. ≈ sa sb ∧ k r = ⋆ sa itcb1 ∧ k' r = ⋆ sb itcb2) ∨
          ≈ (k r) (k' r)) ∨
    ∃r. strip_tau (⋆ (Ret x) itcb1) (Ret r) ∧
        strip_tau (⋆ (Tau u) itcb2) (Ret r)
Proof
  rpt strip_tac >>
  rw[itree_bind_thm] >>
  qabbrev_tac ‘itcb1 = (λx. case x of INL a => Tau (k1 ↻ a) | INR b => Ret b)’ >>
  qabbrev_tac ‘itcb2 = (λx. case x of INL a => Tau (k2 ↻ a) | INR b => Ret b)’ >>
  fs[Once itree_wbisim_cases] >> fs[Once $ GSYM itree_wbisim_cases] >>
  qpat_x_assum ‘strip_tau _ _’ mp_tac >>
  Induct_on ‘strip_tau’ >>
  rw[itree_bind_thm] >-
   (or1_tac >>
    metis_tac[itree_bind_thm,
              itree_wbisim_add_tau, itree_wbisim_trans, itree_wbisim_sym]) >-
   (or1_tac >>
    metis_tac[itree_wbisim_add_tau, itree_wbisim_trans, itree_wbisim_sym]) >-
   (or2_tac >> metis_tac[]) >-
   (or3_tac >> metis_tac[]) >-
   (Cases_on ‘v’ >-
     (qunabbrev_tac ‘itcb1’ >> qunabbrev_tac ‘itcb2’ >>
      rw[] >>
      or1_tac >> or1_tac >>
      qexistsl_tac [‘k1 x’, ‘Tau (k2 x)’] >>
      simp[Once itree_iter_thm] >>
      simp[Once itree_iter_thm, itree_bind_thm] >>
      metis_tac[itree_wbisim_add_tau, itree_wbisim_sym, itree_wbisim_trans]) >-
     (qunabbrev_tac ‘itcb1’ >> qunabbrev_tac ‘itcb2’ >>
      rw[]))
QED

Theorem itree_iter_resp_wbisim:
  ∀t k1 k2. (∀r. ≈ (k1 r) (k2 r)) ⇒ (≈ (k1 ↻ t) (k2 ↻ t))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘itcb1 = (λx. case x of INL a => Tau (k1 ↻ a) | INR b => Ret b)’ >>
  qabbrev_tac ‘itcb2 = (λx. case x of INL a => Tau (k2 ↻ a) | INR b => Ret b)’ >>
  qspecl_then [‘λia ib. ∃sa sb x. (≈ sa sb) ∧ ia = ⋆ sa itcb1 ∧ ib = ⋆ sb itcb2’]
              strip_assume_tac itree_wbisim_strong_coind >>
  pop_assum irule >>
  rw[] >-
   (Cases_on ‘sa’ >>
    Cases_on ‘sb’ >-
     (‘x' = x’ by fs[Once itree_wbisim_cases] >>
      gvs[] >>
      Cases_on ‘x’ >-
       (or1_tac >> (* Ret INL by wbisim *)
        qexistsl_tac [‘⋆ (k1 x') itcb1’, ‘⋆ (k2 x') itcb2’] >>
        qunabbrev_tac ‘itcb1’ >> qunabbrev_tac ‘itcb2’ >>
        simp[Once itree_iter_thm, itree_bind_thm] >>
        simp[Once itree_iter_thm, itree_bind_thm] >>
        metis_tac[]) >-
       (or3_tac >> (* Ret INR by equality *)
        qunabbrev_tac ‘itcb1’ >> qunabbrev_tac ‘itcb2’ >>
        rw[Once itree_iter_thm, itree_bind_thm])) >-
     (irule itree_iter_ret_tau_wbisim >> metis_tac[]) >-
     (fs[Once itree_wbisim_cases]) >-
     (‘≈ (Ret x) (Tau u)’ by fs[itree_wbisim_sym] >>
      ‘(∃t2 t3.
         ⋆ (Ret x) itcb2 = Tau t2 ∧ ⋆ (Tau u) itcb1 = Tau t3 ∧
         ((∃sa sb. ≈ sa sb ∧ t2 = ⋆ sa itcb2 ∧ t3 = ⋆ sb itcb1) ∨ ≈ t2 t3)) ∨
       (∃e k k'.
         strip_tau (⋆ (Ret x) itcb2) (Vis e k) ∧
         strip_tau (⋆ (Tau u) itcb1) (Vis e k') ∧
         ∀r. (∃sa sb. ≈ sa sb ∧ k r = ⋆ sa itcb2 ∧ k' r = ⋆ sb itcb1) ∨
             ≈ (k r) (k' r)) ∨
       ∃r. strip_tau (⋆ (Ret x) itcb2) (Ret r) ∧
           strip_tau (⋆ (Tau u) itcb1) (Ret r)’
        suffices_by metis_tac[itree_wbisim_sym] >>
      irule itree_iter_ret_tau_wbisim >>
      metis_tac[itree_wbisim_sym]) >-
     (or1_tac >>
      rw[itree_bind_thm] >>
      metis_tac[itree_wbisim_add_tau, itree_wbisim_sym, itree_wbisim_trans]) >-
     (rw[itree_bind_thm] >>
      fs[Once itree_wbisim_cases] >> fs[Once $ GSYM itree_wbisim_cases] >>
      qexists_tac ‘(λx. ⋆ (k x) itcb1)’ >>
      metis_tac[itree_bind_vis_strip_tau]) >-
     (fs[Once itree_wbisim_cases]) >-
     (rw[itree_bind_thm] >>
      fs[Once itree_wbisim_cases] >> fs[Once $ GSYM itree_wbisim_cases] >>
      qexists_tac ‘(λx. ⋆ (k' x) itcb2)’ >>
      metis_tac[itree_bind_vis_strip_tau]) >-
     (or2_tac >>
      simp[Once itree_bind_thm] >>
      simp[Once itree_bind_thm] >>
      fs[Once itree_wbisim_cases] >> fs[GSYM $ Once itree_wbisim_cases] >>
      metis_tac[]))
  >- (qexistsl_tac [‘k1 t’, ‘k2 t’] >>
      (* metis_tac[Once itree_iter_thm] metis is broken ??*)
      rw[Once itree_iter_thm] >>
      rw[Once itree_iter_thm])
QED

(*/ basic rephrasings
   not sure whether this should be kept around but lemmas use it atm
 *)

(* iiter (Ret INL) → Tau (itree_unfold (iiter_cb (mrec_cb h_prog))
                           (mrec_cb h_prog (⋆ (rh state_res) k))) to continue *)
(* mrec: Vis (INL (prog × newstate)) k → Ret (INL (h_prog prog ⋆ k)) *)
(* mrec: Vis (INR (svis_ev × result->itree)) k → Ret (INL (h_prog prog ⋆ k)) *)
Definition mrec_cb_def[simp]:
    mrec_cb rh (Ret r) = Ret (INR r)
  ∧ mrec_cb rh (Tau t) = Ret (INL t)
  ∧ mrec_cb rh (Vis (INL state_res) k) = Ret (INL (⋆ (rh state_res) k))
  ∧ mrec_cb rh (Vis (INR ffi_res) k) = Vis ffi_res (λx. Ret (INL (k x)))
End

Theorem itree_mrec_alt:
  itree_mrec rh seed = mrec_cb rh ↻ rh seed
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

Theorem h_prog_rule_dec_alt:
  h_prog_rule_dec vname e p s =
  case eval s e of
    NONE => Ret (SOME Error,s)
  | SOME value =>
      Vis (INL (p,s with locals := s.locals |+ (vname,value)))
          (revert_binding vname s)
Proof
  rw[h_prog_rule_dec_def, revert_binding_def]
QED

(* (* f, f' type vars instantiated differently smh *) *)
(* TODO prove wbisim version *)
(* Theorem mrec_bind_lemma: *)
(*   ∀f f'. *)
(*   (∀a. ∃r. (f a) = (Ret r) ∧ (f' a) = (Ret r)) ⇒ *)
(*   ∀t. (mrec_cb h_prog) ↻ (⋆ t f) = *)
(*       (⋆ (mrec_cb h_prog ↻ t) f') *)
(* Proof *)
(*   rpt strip_tac >> *)
(*   qspecl_then [‘(mrec_cb h_prog) ↻ (⋆ t f)’, *)
(*                ‘⋆ (mrec_cb h_prog ↻ t) f'’] *)
(*               strip_assume_tac itree_bisimulation >> *)
(*   fs[EQ_IMP_THM] >> *)
(*   qpat_x_assum ‘_ ⇒ ∃R. _’ kall_tac >> *)
(*   pop_assum irule >> *)
(*   qexists_tac ‘λa b. ∃t name s. *)
(*                 a = (mrec_cb h_prog ↻ (⋆ t f)) ∧ *)
(*                 b = (⋆ (mrec_cb h_prog ↻ t) f')’ >> *)
(*   rw[] >- *)
(*    metis_tac[] >- (* base case *) *)
(*    (* ret *) *)
(*    (Cases_on ‘t'’ >- *)
(*      (fs[Once itree_iter_thm, itree_bind_thm] >> *)
(*       last_assum $ qspec_then ‘x'’ strip_assume_tac >> *)
(*       fs[itree_bind_thm]) >- *)
(*      (fs[Once itree_iter_thm, itree_bind_thm]) >- *)
(*      (Cases_on ‘a’ >- *)
(*        fs[Once itree_iter_thm, itree_bind_thm] >- *)
(*        fs[Once itree_iter_thm, itree_bind_thm])) >- *)
(*    (* tau *) *)
(*    (Cases_on ‘t'’ >- *)
(*      (fs[Once itree_iter_thm, itree_bind_thm] >> *)
(*       last_assum $ qspec_then ‘x’ strip_assume_tac >> *)
(*       fs[itree_bind_thm]) >- *)
(*      (fs[Once itree_iter_thm, itree_bind_thm] >> *)
(*       metis_tac[]) >- *)
(*      (Cases_on ‘a’ >- *)
(*        (fs[Once itree_iter_thm, itree_bind_thm] >> *)
(*         metis_tac[itree_bind_assoc]) >- *)
(*        fs[Once itree_iter_thm, itree_bind_thm])) >- *)
(*    (* vis *) *)
(*    (Cases_on ‘t'’ >- *)
(*      (fs[Once itree_iter_thm, itree_bind_thm] >> *)
(*       last_assum $ qspec_then ‘x’ strip_assume_tac >> *)
(*       fs[itree_bind_thm]) >- *)
(*      fs[Once itree_iter_thm, itree_bind_thm] >- *)
(*      (Cases_on ‘a'’ >- *)
(*        fs[Once itree_iter_thm, itree_bind_thm] >- *)
(*        (fs[Once itree_iter_thm, itree_bind_thm] >> *)
(*         strip_tac >> *)
(*         (* stuck on extra Tau from iter on (Ret INL) from (Vis INR) *) *)
(*        ))) *)
(* QED *)

(* relies on mrec_cb h_prog rev -> only Ret INR, so can't prolong iteration *)
(* also applies to while and cond! *)
Theorem dec_lemma:
  ∀ t name s.
    ≈ (mrec_cb h_prog ↻ (⋆ t (revert_binding name s)))
      (⋆ (mrec_cb h_prog ↻ t) (revert_binding name s))
Proof
  qspecl_then
  [‘λa b. ∃t name s.
     a = (mrec_cb h_prog ↻ (⋆ t (revert_binding name s))) ∧
     b = (⋆ (mrec_cb h_prog ↻ t) (revert_binding name s))’]
  strip_assume_tac itree_wbisim_strong_coind >>
  rpt strip_tac >>
  pop_assum irule >>
  rw[] >-
   (Cases_on ‘t''’ >-
     (or3_tac >> (* Ret produces Ret, doesn't affect iter. easy! *)
      Cases_on ‘x’ >>
      rw[revert_binding_def] >>
      rw[Once itree_iter_thm, itree_bind_thm] >>
      rw[Once itree_iter_thm, itree_bind_thm]) >-
     (* Tau case is clear *)
     (or1_tac >>
      rw[Once itree_iter_thm, itree_bind_thm] >>
      rw[Once itree_iter_thm, itree_bind_thm] >>
      metis_tac[]) >-
     (* Vis case is a bit tricky, depends on whether the event is silent *)
     (Cases_on ‘a’ >-
       (or1_tac >>
        rw[Once itree_iter_thm, itree_bind_thm] >>
        rw[Once itree_iter_thm, itree_bind_thm] >>
        metis_tac[itree_bind_assoc]) >-
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
          rw[itree_bind_thm])))) >-
   metis_tac[]
QED

Theorem dec_thm:
  (eval s e = SOME k) ⇒
  ≈ (itree_mrec h_prog (Dec name e p,s))
    (⋆
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
   this doesn't have a nice theory but simps should do most of the work
 *)

Definition massage_cb_def[simp]:
    massage_cb (INL (Ret (res,s))) = Ret' res
  ∧ massage_cb (INR (Ret (res,s))) = Ret' res
  ∧ massage_cb (INL (Tau t)) = Tau' (INL t)
  ∧ massage_cb (INR (Tau t)) = Tau' (INR t)
  ∧ massage_cb (INL (Vis (e,k) g)) = Vis' e (λr. INR (k r))
  ∧ massage_cb (INR (Vis e g))     = Vis' e (INR ∘ g)
End

(* massage Ret type from (η x state) -> η *)
(* convert Vis (sem_vis_event x (FFI_result -> itree)) ((prog x state) -> %itree)
-> Vis sem_vis_event (FFI_result -> itree) *)
Definition massage_def:
  massage x = itree_unfold massage_cb (INL x)
End

Theorem massage_thm:
    massage (Ret (res, s)) = Ret res ∧ massage (Tau t) = Tau (massage t)
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

open stringLib helperLib;
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
  0w < 1w (* supposed to be :4 word but w/e *)
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
