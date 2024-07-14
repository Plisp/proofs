open bossLib;
open arithmeticTheory;
open relationTheory;
open fixedPointTheory;
open pred_setTheory;
open pairTheory;

val _ = new_theory "upto";

open posetTheory;

Theorem subset_poset:
  poset (UNIV, $SUBSET)
Proof
  rw[poset_def, SUBSET_ANTISYM]
QED

Definition pcompatible_def:
  pcompatible p b f = (monotonic p b ∧ monotonic p f ∧
                       ∀x. (x ∈ carrier p) ⇒ relation p (f(b x)) (b(f x)))
End

Definition compatible_def:
  compatible b f = (monotone b ∧ monotone f ∧ ∀x. f(b x) ⊆ b(f x))
End

Definition companion_def:
  companion b = λX. BIGUNION {f X | f | compatible b f}
End

Theorem compatible_below_companion:
  compatible b f ⇒ f x ⊆ (companion b) x
Proof
  rw[companion_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem companion_mono[simp]:
  monotone b
⇒ monotone (companion b)
Proof
  rw[monotone_def, companion_def, SUBSET_DEF, PULL_EXISTS] >>
  metis_tac[compatible_def, monotone_def, SUBSET_DEF]
QED

Theorem compatible_companion:
  monotone b ⇒ compatible b (companion b)
Proof
  rw[compatible_def,companion_def,SUBSET_DEF] >>
  first_assum drule >>
  qmatch_goalsub_abbrev_tac ‘_ ∈ b a1 ⇒ _ ∈ b a2’ >>
  ‘a1 ⊆ a2’ by (rw[Abbr ‘a1’, Abbr ‘a2’,SUBSET_DEF,PULL_EXISTS] >> metis_tac[]) >>
  metis_tac[monotone_def,SUBSET_DEF]
QED

Theorem compatible_id:
  monotone b ⇒ compatible b I
Proof
  rw[compatible_def, monotone_def]
QED

Theorem compatible_b:
  monotone b ⇒ compatible b b
Proof
  rw[compatible_def]
QED

Theorem compatible_const_gfp:
  monotone b ⇒ compatible b (K (gfp b))
Proof
  rw[compatible_def, monotone_def, gfp_greatest_fixedpoint]
QED

Theorem compatible_compose:
  monotone b
⇒ compatible b f ∧ compatible b g
⇒ compatible b (f ∘ g)
Proof
  rw[compatible_def, PULL_EXISTS, monotone_def] >>
  metis_tac[SUBSET_TRANS]
QED

Theorem companion_gt:
  monotone b ⇒ x ⊆ companion b x
Proof
  rpt strip_tac >>
  ho_match_mp_tac compatible_below_companion >>
  metis_tac[compatible_id]
QED

Theorem companion_idem:
  monotone b
⇒ companion b ((companion b) x) = (companion b) x
Proof
  rw[SET_EQ_SUBSET] >-
   (‘compatible b (companion b ∘ companion b)’
      by rw[compatible_compose, compatible_companion] >>
    ho_match_mp_tac compatible_below_companion >>
    metis_tac[])
  >- rw[companion_gt]
QED

(* TODO put in fixedpointtheory *)
Theorem monotone_comp:
  monotone f ∧ monotone g ⇒ monotone (f ∘ g)
Proof
  rw[monotone_def]
QED

Theorem companion_bot_gfp:
  monotone b
  ⇒ companion b ∅ = gfp b
Proof
  rw[SET_EQ_SUBSET] >-
   (* t⊥ ≤ tb⊥ ≤ bt⊥ *)
   (irule gfp_coinduction >>
    simp[] >>
    match_mp_tac SUBSET_TRANS >>
    drule (REWRITE_RULE [companion_mono,compatible_def] compatible_companion) >>
    strip_tac >>
    first_assum $ irule_at Any >> (* Pat ‘’ *)
    irule $ iffLR monotone_def >>
    rw[])
  >-
   (drule_then strip_assume_tac compatible_const_gfp >>
    simp[companion_def] >>
    rw[SUBSET_DEF, PULL_EXISTS] >> (* note: PULL_EXISTS to toplevel instantiates *)
    metis_tac[combinTheory.K_DEF])
QED

Definition enhance_def:
  enhance b = b ∘ (companion b)
End

Theorem companion_coinduct:
  monotone b
  ⇒ x ⊆ enhance b x
  ⇒ x ⊆ gfp b
Proof
  rw[enhance_def] >>
  ‘(companion b) x ⊆ gfp b’ suffices_by metis_tac[companion_gt, SUBSET_TRANS] >>
  irule gfp_coinduction >>
  simp[] >>
  drule companion_mono >>
  strip_tac >>
  irule SUBSET_TRANS >>
  qexists_tac ‘(companion b) (b (companion b x))’ >>
  CONJ_TAC >- (fs[monotone_def, companion_mono]) >>
  irule SUBSET_TRANS >>
  qexists_tac ‘b (companion b (companion b x))’ >>
  CONJ_TAC >-
   (fs[REWRITE_RULE [companion_mono,compatible_def] compatible_companion]) >>
  gvs[monotone_def, companion_idem, combinTheory.o_DEF]
QED

Theorem enhanced_gfp:
  monotone b
  ⇒ gfp (enhance b) = gfp b
Proof
  rw[enhance_def, SET_EQ_SUBSET] >-
   (drule_then match_mp_tac companion_coinduct >>
    ‘monotone (enhance b)’
      by metis_tac[monotone_def, enhance_def, monotone_comp, companion_mono] >>
    fs[enhance_def] >>
    metis_tac[cj 1 gfp_greatest_fixedpoint, combinTheory.o_DEF, SET_EQ_SUBSET])
  >-
   (irule gfp_coinduction >>
    rw[monotone_comp, companion_mono] >>
    simp[SimpL “$SUBSET”, Once $ GSYM gfp_greatest_fixedpoint] >>
    irule $ iffLR monotone_def >>
    rw[companion_gt])
QED

(* parameterized *)
Definition semicompatible_def:
  semicompatible b f = ∀x. f x ⊆ companion b x
End

Theorem param_coind_init:
  monotone b
  ⇒ {(xs,ys)} ⊆ companion b ∅
  ⇒ (xs,ys) ∈ gfp b
Proof
  rw[companion_bot_gfp]
QED

Theorem param_coind_done:
  monotone b
  ⇒ y ⊆ x ⇒ y ⊆ companion b x
Proof
  metis_tac[companion_gt, SUBSET_TRANS]
QED

Theorem param_coind_upto_f:
  monotone b
  ⇒ y ⊆ f (companion b x) ∧ semicompatible b f
  ⇒ y ⊆ companion b x
Proof
  rw[semicompatible_def] >>
  (* matches drule precondition against assumptions *)
  drule_then match_mp_tac SUBSET_TRANS >>
  match_mp_tac SUBSET_TRANS >>
  first_assum $ irule_at (Pos hd) >>
  simp[companion_idem]
QED

Definition wcontinuous_def:
  wcontinuous b = ∀P. (b (BIGINTER P) = BIGINTER { b s | s ∈ P })
End

Theorem continuous_mono:
  wcontinuous b ⇒ monotone b
Proof
  rw[wcontinuous_def, monotone_def] >>
  ‘X = BIGINTER { X; Y }’ by rw[BIGINTER_INTER, SUBSET_INTER1] >>
  ‘b (BIGINTER {X; Y}) ⊆ b Y’ suffices_by metis_tac[] >>
  pop_last_assum $ qspec_then ‘{X; Y}’ strip_assume_tac >>
  ‘BIGINTER {b s | s ∈ {X; Y}} ⊆ b Y’ suffices_by metis_tac[] >>
  ‘BIGINTER {b s | s ∈ {X; Y}} = BIGINTER {b X; b Y}’ by cheat >>
  rw[]
QED

Theorem continuous_fixpoint:
  wcontinuous b ⇒ gfp b = BIGINTER (λx. ∃n. x = FUNPOW b n (K T))
Proof
  rw[Once SET_EQ_SUBSET] >-
   (rw[SUBSET_DEF] >>
    pop_assum mp_tac >>
    ‘gfp b ⊆ FUNPOW b n (K T)’ suffices_by metis_tac[GSYM SUBSET_DEF] >>
    Induct_on ‘n’ >- rw[combinTheory.K_DEF, SUBSET_DEF] >>
    drule continuous_mono >> strip_tac >>
    rw[arithmeticTheory.FUNPOW_SUC] >>
    simp[SimpL “$SUBSET”, Once $ GSYM gfp_greatest_fixedpoint] >>
    fs[monotone_def]) >>
  irule (cj 2 gfp_greatest_fixedpoint) >>
  rw[continuous_mono] >>
  cheat
QED

Theorem companion_eq:
  ∀b. wcontinuous b
      ⇒ companion b = (λx. BIGINTER (λs. ∃n. s = FUNPOW b n (K T) ∧ x ⊆ s))
Proof
  rw[Once FUN_EQ_THM, SET_EQ_SUBSET] >-
   (rw[companion_def, SUBSET_DEF, PULL_EXISTS] >>
    subgoal ‘FUNPOW b n (f (K T)) ⊆ FUNPOW b n (K T)’ >-
     (rw[combinTheory.K_DEF]
     )
    Induct_on ‘n’ >- rw[combinTheory.K_DEF] >>
    rw[]
   )
  >-
   (ho_match_mp_tac compatible_below_companion >>
    rw[compatible_def] >-
     (rw[monotone_def, SUBSET_DEF, PULL_EXISTS]) >>
    rw[SUBSET_DEF, PULL_EXISTS]
   )
QED

Definition connection_join:
  connection_join b g = λx. BIGUNION { f x | ∀y. f (b y) ⊆ b (g y) }
End

Definition pointwise_monotone_def:
  pointwise_monotone higher_functional
  = (∀f g. (∀x. f x ⊆ g x) ⇒ ∀x. (higher_functional f) x ⊆ (higher_functional g) x)
End

Theorem connection_join_mono:
  monotone b
  ⇒ pointwise_monotone (connection_join b)
Proof
  rw[monotone_def, pointwise_monotone_def] >>
  rw[connection_join, Once SUBSET_DEF, PULL_EXISTS] >>
  qexists_tac ‘f'’ >> rw[] >>
  pop_assum $ qspec_then ‘y’ strip_assume_tac >>
  ‘b (f y) ⊆ b (g y)’ suffices_by metis_tac[SUBSET_TRANS] >>
  metis_tac[]
QED

Theorem lemma6_2:
  (∀x. f x ⊆ (B g) x) = (∀x. f b x ⊆ b g x)
Proof
  rw[]
QED

Theorem param_coind:
  monotone b
  ⇒ y ⊆ b (companion b (x ∪ y)) ⇒ y ⊆ (companion b) x
Proof

QED














(* example *)

open llistTheory;
Definition llist_functional:
  llist_functional R = (* in the paper, llist_functional is called "b" *)
  ({[||],[||]} ∪ {(x:::xs,y:::ys) | x = y ∧ (xs,ys) ∈ R})
End

Theorem llist_inversion:
  (x, y) ∈ llist_functional R
  ⇒ (x = [||] ∧ y = [||]) ∨
    (∃e xs ys. x = e:::xs ∧ y = e:::ys ∧ (xs,ys) ∈ R)
Proof
  rw[llist_functional]
QED

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
  rw[monotone_def, itree_wbisim_functional, pred_setTheory.SUBSET_DEF] >>
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
  simp[ones_def] >> simp[Once LUNFOLD]
QED

Theorem ones'_thm:
  ones' = 1:::1:::ones'
Proof
  simp[ones'_def] >> ntac 2 $ simp[Once LUNFOLD]
QED

Theorem ones_eq_ones':
  ones = ones'
Proof
  simp[Once LLIST_BISIMULATION] >>
  qexists_tac ‘CURRY {(ones,ones'); (ones,1:::ones')}’ >>
  rw[]
  THEN1 (PURE_ONCE_REWRITE_TAC[ones_thm,ones'_thm] >>
         simp[] >>
         disj2_tac >>
         metis_tac[ones_thm,ones'_thm]
        )
  THEN1 (PURE_ONCE_REWRITE_TAC[ones_thm] >> simp[] >>
         metis_tac[ones_thm])
QED

TODO recover this
Theorem companion_coinduct':

Proof

QED

Theorem companion_coinduct_itree:
  ∀t t' R.
    (t,t') ∈ R ∧
    R ⊆ itree_wbisim_functional (companion itree_wbisim_functional R)
    ⇒ itree_wbisim t t'
Proof
  rpt strip_tac >>
  assume_tac monotone_itree_functional >>
  qspecl_then [‘itree_wbisim_functional’,‘R’] strip_assume_tac companion_coinduct >>
  gvs[itree_functional_corres, SUBSET_DEF, pairTheory.ELIM_UNCURRY] >>
  metis_tac[FST, SND, PAIR]
QED

Theorem ones_eq_ones':
  ones = ones'
Proof
  match_mp_tac companion_coinduct' >>
  qexists_tac ‘{(ones,ones')}’ >>
  rw[llist_functional] >>
  PURE_ONCE_REWRITE_TAC[ones_thm,ones'_thm] >> simp[] >>
  simp[companion_def] >>
  irule_at (Pos last) compatible_cons >>
  simp[] >> disj2_tac >>
  metis_tac[ones_thm,ones'_thm]
QED

Theorem compatible_cons:
  compatible $ (λR. R ∪ {([||],[||])} ∪ {x:::xs,y:::ys | x = y ∧ (xs,ys) ∈ R})
Proof
  rw[compatible_def,monotone_def,SUBSET_DEF,PULL_EXISTS] >>
  gvs[llist_functional]
QED

Definition cons_rel_def:
  cons_rel R = {x:::xs,y:::ys | x = y ∧ (xs,ys) ∈ R}
End

Theorem semicompatible_cons:
  semicompatible cons_rel
Proof
  rw[semicompatible_def,SUBSET_DEF,companion_def,cons_rel_def] >>
  irule_at (Pos last) compatible_cons >>
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
  rw[semicompatible_def,companion_def,SUBSET_DEF,PULL_EXISTS] >>
  irule_at (Pos last) compatible_id >>
  simp[]
QED

Theorem ones_eq_ones':
  ones = ones'
Proof
  match_mp_tac param_coind_init >>
  match_mp_tac param_coind >>
  SIMP_TAC std_ss [Once ones'_thm, Once ones_thm,llist_functional_cons] >>
  SIMP_TAC std_ss [Once ones_thm] >>
  match_mp_tac param_coind_upto_f >>
  irule_at Any semicompatible_cons >>
  SIMP_TAC std_ss [cons_rel_cons] >>
  match_mp_tac param_coind_done >> rw[]
QED
