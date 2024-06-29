open bossLib;
open llistTheory;
open relationTheory;
open fixedPointTheory;
open pred_setTheory;
open pairTheory;

val _ = new_theory "demo";

Definition llist_functional:
  llist_functional R = (* in the paper, llist_functional is called "b" *)
  ({[||],[||]} ∪ {(x:::xs,y:::ys) | x = y ∧ (xs,ys) ∈ R})
End

open itreeTauTheory;

Definition itree_wbisim_functional:
  itree_wbisim_functional R =
  ({ (t,t') | ∃r. strip_tau t (Ret r) ∧ strip_tau t' (Ret r)}
 ∪ { (t,t') | ∃e k k'. strip_tau t (Vis e k) ∧ strip_tau t' (Vis e k') ∧
                       ∀r. (k r, k' r) ∈ R }
 ∪ { (Tau t, Tau t') | (t,t') ∈ R })
End

(*  llist_functional ∅
      the set of all list pairs such that either:
      - they're both empty, or
      - they both have the same head
    llist_functional(llist_functional ∅)
      the set of all list pairs such that either:
      - their two outermost constructors are the same

    We're interested in fixed points of llist_functional

      lfp llist_functional    <--- equality between finite lists

      gfp llist_functional    <--- equality between finite or infinite lists
  *)

Theorem monotone_llist_functional[simp]:
  monotone llist_functional
Proof
  rw[monotone_def,llist_functional,pred_setTheory.SUBSET_DEF]
QED

Theorem monotone_itree_functional[simp]:
  monotone itree_wbisim_functional
Proof
  rw[monotone_def,itree_wbisim_functional,pred_setTheory.SUBSET_DEF] >>
  cheat
QED

Theorem llist_functional_correct:
  gfp llist_functional = UNCURRY $=
Proof
  simp[SET_EQ_SUBSET] \\
  conj_tac THEN1
   (simp[SUBSET_DEF,Once FUN_EQ_THM] \\ Cases \\
    strip_tac \\ gvs[IN_DEF] \\
    match_mp_tac LLIST_BISIMULATION_I \\
    qexists_tac ‘CURRY $ gfp llist_functional’ \\
    rw[] \\
    pop_assum mp_tac \\
    dep_rewrite.DEP_ONCE_REWRITE_TAC [GSYM $ cj 1 gfp_greatest_fixedpoint] \\
    conj_tac THEN1 simp[] \\
    simp[Once llist_functional] \\
    rw[] \\
    simp[cj 1 gfp_greatest_fixedpoint] \\
    fs[IN_DEF]) \\
  match_mp_tac $ MP_CANON gfp_coinduction \\
  simp[SUBSET_DEF] \\
  Cases \\ rw[] \\
  simp[llist_functional] \\
  Cases_on ‘q’ \\ gvs[]
QED

Theorem itree_functional_corres:
  gfp itree_wbisim_functional = UNCURRY itree_wbisim
Proof
  cheat
QED

Definition compatible_def:
  compatible b f = (monotone b ∧ monotone f ∧ ∀x. f(b x) ⊆ b(f x))
End

Definition companion_def:
  companion b = λX. BIGUNION {f X | compatible b f}
End

Theorem companion_mono[simp]:
  monotone b ⇒ monotone (companion b)
Proof
  rw[monotone_def,companion_def,SUBSET_DEF,PULL_EXISTS] >>
  qexists_tac ‘f’ >>
  gvs[compatible_def] >>
  metis_tac[monotone_def,SUBSET_DEF]
QED

Theorem compatible_companion:
  monotone b ⇒ compatible b (companion b)
Proof
  rw[compatible_def,companion_def,SUBSET_DEF] >>
  first_assum drule >>
  qmatch_goalsub_abbrev_tac ‘_ ∈ b a1 ⇒ _ ∈ b a2’ >>
  ‘a1 ⊆ a2’ by (rw[Abbr ‘a1’, Abbr ‘a2’,SUBSET_DEF,PULL_EXISTS] >> metis_tac[]) >>
  metis_tac[monotone_def,monotone_llist_functional,SUBSET_DEF]
QED

Theorem compatible_id:
  monotone b ⇒ compatible b I
Proof
  rw[compatible_def,monotone_def]
QED

Theorem compatible_compose:
  monotone b ⇒ compatible b f ∧ compatible b g ⇒ compatible b (f ∘ g)
Proof
  rw[compatible_def,PULL_EXISTS,monotone_def] >>
  metis_tac[SUBSET_TRANS]
QED





(* TODO *)
Theorem companion_idem:
  ((companion b) ∘ (companion b)) R = (companion b) R
Proof
  rw[SET_EQ_SUBSET]
  THEN1 (rw[Once companion_def,SUBSET_DEF] \\
         rw[companion_def,PULL_EXISTS] \\
         qexists_tac ‘f o companion b’ \\
         simp[compatible_compose,compatible_companion])
  THEN1 (rw[SUBSET_DEF] \\ rw[Once companion_def,PULL_EXISTS] \\
         irule_at Any compatible_id \\
         simp[])
QED

Theorem companion_coinduct:
  ∀R.
    R ⊆ llist_functional(companion R)
    ⇒ R ⊆ gfp llist_functional
Proof
  rpt strip_tac  \\
  ‘companion R ⊆ gfp llist_functional’
    by(match_mp_tac $ MP_CANON gfp_coinduction \\
       simp[] \\
       drule $ REWRITE_RULE [monotone_def] companion_mono \\
       strip_tac \\
       drule_then match_mp_tac SUBSET_TRANS \\
       match_mp_tac SUBSET_TRANS \\
       irule_at (Pos hd) $ REWRITE_RULE [companion_mono,compatible_def] compatible_companion \\
       simp[companion_idem]) \\
  ‘R ⊆ companion R’
    by(rw[companion_def,SUBSET_DEF,PULL_EXISTS] \\
       irule_at Any compatible_id \\
       simp[]) \\
  metis_tac[SUBSET_TRANS]
QED

Theorem companion_coinduct':
  ∀ll1 ll2 R.
    (ll1,ll2) ∈ R ∧
    R ⊆ llist_functional(companion R)
    ⇒ ll1 = ll2
Proof
  rpt strip_tac  \\
  drule companion_coinduct \\
  gvs[llist_functional_correct,SUBSET_DEF,pairTheory.ELIM_UNCURRY] \\
  metis_tac[FST,SND,PAIR]
QED



(* parameterized *)
Definition semicompatible_def:
  semicompatible R = ∀X. R X ⊆ companion b X
End

Theorem param_coind_init:
  {(xs,ys)} ⊆ companion ∅ ⇒ xs = ys
Proof
  strip_tac \\
  match_mp_tac companion_coinduct' \\
  fs[] \\
  first_x_assum $ irule_at Any \\
  simp[companion_idem] \\
  rw[Once SUBSET_DEF] \\
  gvs[companion_def,compatible_def] \\
  ‘x ∈ f(llist_functional ∅)’
    by(gvs[monotone_def,SUBSET_DEF] \\
       first_x_assum $ match_mp_tac o MP_CANON \\
       first_x_assum $ irule_at $ Pos last \\
       rw[]) \\
  gvs[SUBSET_DEF] \\
  first_assum dxrule \\
  match_mp_tac $ REWRITE_RULE[monotone_def,SUBSET_DEF]monotone_llist_functional \\
  rw[PULL_EXISTS] \\
  metis_tac[]
QED

Theorem param_coind_done:
  ∀R S. R ⊆ S ⇒ R ⊆ companion S
Proof
  rw[companion_def,SUBSET_DEF,PULL_EXISTS] \\
  irule_at (Pos last) compatible_id \\
  simp[]
QED

Theorem param_coind_upto_f:
  ∀R S f. R ⊆ f(companion S) ∧ semicompatible f ⇒ R ⊆ companion S
Proof
  rw[semicompatible_def] \\
  drule_then match_mp_tac SUBSET_TRANS \\
  match_mp_tac SUBSET_TRANS \\
  first_x_assum $ irule_at $ Pos hd \\
  simp[companion_idem]
QED

Theorem llist_functional_semicompat:
  llist_functional R ⊆ companion R
Proof
  rw[companion_def,SUBSET_DEF,PULL_EXISTS] \\
  first_x_assum $ irule_at $ Pos hd \\
  rw[compatible_def]
QED

Theorem param_coind:
  ∀R S. R ⊆ llist_functional(companion(R ∪ S)) ⇒ R ⊆ companion S
Proof
  cheat
QED








(* example *)

Definition ones_def:
  ones = LUNFOLD (K $ SOME ((),1)) ()
End

Definition ones'_def:
  ones' = LUNFOLD (λx. SOME (¬x,1)) T
End

(* pretend these are the definitions: *)

Theorem ones_thm:
  ones = 1:::ones
Proof
  simp[ones_def] \\ simp[Once LUNFOLD]
QED

Theorem ones'_thm:
  ones' = 1:::1:::ones'
Proof
  simp[ones'_def] \\ ntac 2 $ simp[Once LUNFOLD]
QED

Theorem ones_eq_ones':
  ones = ones'
Proof
  simp[Once LLIST_BISIMULATION] \\
  qexists_tac ‘CURRY {(ones,ones'); (ones,1:::ones')}’ \\
  rw[]
  THEN1 (PURE_ONCE_REWRITE_TAC[ones_thm,ones'_thm] \\
         simp[] \\
         disj2_tac \\
         metis_tac[ones_thm,ones'_thm]
        )
  THEN1 (PURE_ONCE_REWRITE_TAC[ones_thm] \\ simp[] \\
         metis_tac[ones_thm])
QED

Theorem ones_eq_ones':
  ones = ones'
Proof
  match_mp_tac companion_coinduct' \\
  qexists_tac ‘{(ones,ones')}’ \\
  rw[llist_functional] \\
  PURE_ONCE_REWRITE_TAC[ones_thm,ones'_thm] \\ simp[] \\
  simp[companion_def] \\
  irule_at (Pos last) compatible_cons \\
  simp[] \\ disj2_tac \\
  metis_tac[ones_thm,ones'_thm]
QED

Theorem compatible_cons:
  compatible $ (λR. R ∪ {([||],[||])} ∪ {x:::xs,y:::ys | x = y ∧ (xs,ys) ∈ R})
Proof
  rw[compatible_def,monotone_def,SUBSET_DEF,PULL_EXISTS] \\
  gvs[llist_functional]
QED

Definition cons_rel_def:
  cons_rel R = {x:::xs,y:::ys | x = y ∧ (xs,ys) ∈ R}
End

Theorem semicompatible_cons:
  semicompatible cons_rel
Proof
  rw[semicompatible_def,SUBSET_DEF,companion_def,cons_rel_def] \\
  irule_at (Pos last) compatible_cons \\
  rw[]
QED

Theorem llist_functional_cons:
  {(x:::xs,x:::ys)} ⊆ llist_functional R
  ⇔ {(xs,ys)} ⊆ R
Proof
  rw[llist_functional,SUBSET_DEF]
QED

Theorem cons_rel_cons:
  {(x:::xs,x:::ys)} ⊆ cons_rel R
  ⇔ {(xs,ys)} ⊆ R
Proof
  rw[cons_rel_def,SUBSET_DEF]
QED

Theorem semicompatible_id:
  semicompatible I
Proof
  rw[semicompatible_def,companion_def,SUBSET_DEF,PULL_EXISTS] \\
  irule_at (Pos last) compatible_id \\
  simp[]
QED

Theorem ones_eq_ones':
  ones = ones'
Proof
  match_mp_tac param_coind_init \\
  match_mp_tac param_coind \\
  SIMP_TAC std_ss [Once ones'_thm, Once ones_thm,llist_functional_cons] \\
  SIMP_TAC std_ss [Once ones_thm] \\
  match_mp_tac param_coind_upto_f \\
  irule_at Any semicompatible_cons \\
  SIMP_TAC std_ss [cons_rel_cons] \\
  match_mp_tac param_coind_done \\ rw[]
QED
