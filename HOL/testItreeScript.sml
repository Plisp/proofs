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
 *
 * note: programs/simps/rewrites getting stuck in general is hard to predict and
 * annoying, proving strong normalization is the only way out.
 * note: don't worry about the itree repr
 *)

open HolKernel boolLib bossLib BasicProvers;
open arithmeticTheory;
open itreeTauTheory;
open panSemTheory; (* eval_def *)
open panItreeSemTheory;

(* open monadsyntax; *)
(* val _ = *)
(*     monadsyntax.declare_monad ( *)
(*       "itree_monad", *)
(*       { bind = “itree_bind”, ignorebind = NONE, unit = “Ret”, *)
(*         guard = NONE, choice = NONE, fail = NONE} *)
(*     ) *)
(* val _ = monadsyntax.temp_enable_monad "itree_monad"; *)

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

Overload trigger[local] = “itree_trigger”;
Theorem trigger:
  trigger event = Vis event Ret
Proof
  rw[itree_trigger_def]
QED

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

(*/ misc abstract nonsense
   just to have a richer equational theory for wbisim
 *)

Theorem itree_bind_trigger:
  ⋆ (trigger e) k = Vis e k
Proof
  rw[itree_trigger_def, itree_bind_thm, FUN_EQ_THM]
QED

Theorem itree_wbisim_vis:
  ∀e k1 k2. (∀r. ≈ (k1 r) (k2 r)) ⇒ ≈ (Vis e k1) (Vis e k2)
Proof
  metis_tac[strip_tau_cases, itree_wbisim_cases]
QED

(* TODO itree_wbisim_tau is overloaded! merged. change later *)
Theorem itree_wbisim_tau_eq:
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
      metis_tac[itree_wbisim_trans, itree_wbisim_sym, itree_wbisim_tau_eq] >>
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
  ∀a b k1 k2. (≈ a b) ∧ (∀r. ≈ (k1 r) (k2 r)) ⇒ (≈ (⋆ a k1) (⋆ b k2))
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
              itree_wbisim_tau_eq, itree_wbisim_trans, itree_wbisim_sym]) >-
   (or1_tac >>
    metis_tac[itree_wbisim_tau_eq, itree_wbisim_trans, itree_wbisim_sym]) >-
   (or2_tac >> metis_tac[]) >-
   (or3_tac >> metis_tac[]) >-
   (Cases_on ‘v’ >-
     (qunabbrev_tac ‘itcb1’ >> qunabbrev_tac ‘itcb2’ >>
      rw[] >>
      or1_tac >> or1_tac >>
      qexistsl_tac [‘k1 x’, ‘Tau (k2 x)’] >>
      simp[Once itree_iter_thm] >>
      simp[Once itree_iter_thm, itree_bind_thm] >>
      metis_tac[itree_wbisim_tau_eq, itree_wbisim_sym, itree_wbisim_trans]) >-
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
      (* (pure)_rewrite_tac more basic *)
      rpt $ qpat_x_assum ‘Abbrev _’
          $ assume_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def] >>
      pop_assum mp_tac >>
      drule itree_iter_ret_tau_wbisim >>
      rpt strip_tac >>
      first_x_assum drule >>
      disch_then drule >>
      (* irule (a ∧ (b -> c)) -> (a -> b) -> c >> CONJ_TAC *)
      impl_tac >> metis_tac[itree_wbisim_sym]) >-
     (or1_tac >>
      rw[itree_bind_thm] >>
      metis_tac[itree_wbisim_tau_eq, itree_wbisim_sym, itree_wbisim_trans]) >-
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

(*/
  coinduction
 *)

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

Definition iterate_def:
  iterate emit succ zero =
  itree_unfold (λs'. Vis' (emit s') (λ_. (succ s'))) zero
End

Definition even_spec_def:
  even_spec k = iterate (λx. if EVEN x then "even" else "odd") (λn. 1 + n) k
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
  CONV_TAC $ LHS_CONV $ REWRITE_CONV[iterate_def] >>
  rw[itree_unfold] >>
  rw[combinTheory.o_DEF] >>
  rw[FUN_EQ_THM] >>
  rw[itree_unfold] >-
   (metis_tac[even_add1]) >-
   (rw[combinTheory.o_DEF] >>
    rw[iterate_def])
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
  rw[] >> gvs[even_spec_def, iterate_def, Once itree_unfold] >-
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
  even_spec 0 = ⋆ (⋆ (trigger "even")
                     (λ_. (trigger "odd")))
                  (λ_. even_spec 0)
Proof
  rw[Once even_spec_unfold] >>
  rw[itree_bind_trigger] >>
  rw[itree_bind_thm] >>
  rw[FUN_EQ_THM] >>
  rw[itree_bind_trigger] >>
  rw[FUN_EQ_THM] >>
  qspec_then ‘0’ mp_tac even_spec_plus2 >>
  rw[]
QED
