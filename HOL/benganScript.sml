(* written up by Johannes *)

open bossLib itreeTauTheory;

val _ = new_theory "bengan"

Definition wupto_def:
  wupto R t1 t4 = ∃t2 t3. itree_wbisim t1 t2 ∧ R t2 t3 ∧ itree_wbisim t3 t4
End

(* Let's pretend it's sound and do silly things with it*)
Theorem wbisim_upto_coind:
  ∀R.
    (∀t1 t2.
       R t1 t2 ⇒
       (∃t t'. t1 = Tau t ∧ t2 = Tau t' ∧ wupto R t t') ∨
       (∃e k k'.
          strip_tau t1 (Vis e k) ∧ strip_tau t2 (Vis e k') ∧
          ∀r. wupto R (k r) (k' r)) ∨
       ∃r. strip_tau t1 (Ret r) ∧ strip_tau t2 (Ret r)) ⇒
    ∀t1 t2. R t1 t2 ⇒ itree_wbisim t1 t2
Proof
  cheat
QED

(* Something akin to Bengt Jonsson's counterexample, the prover can observe Taus *)
Theorem bengan:
  itree_wbisim (Tau $ Ret T) (Tau $ Ret F)
Proof
  reverse $ subgoal ‘∀t1 t2. t1 = Tau $ Ret T ∧ t2 = (Tau $ Ret F) ⇒ itree_wbisim t1 t2’
  >- metis_tac[] >>
  ho_match_mp_tac wbisim_upto_coind >>
  rw[wupto_def] >>
  metis_tac[itree_wbisim_tau,itree_wbisim_refl,itree_wbisim_sym]
QED

Theorem falsity:
  F
Proof
  mp_tac bengan >>
  ntac 2 $ rw[Once itree_wbisim_cases]
QED

val _ = export_theory()
