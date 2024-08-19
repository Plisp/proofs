open arithmeticTheory;
open relationTheory;
open fixedPointTheory;
open pred_setTheory;
open pairTheory;
open posetTheory;

val _ = new_theory "upto";

(* TODO put in fixedpointtheory *)
Theorem monotone_comp:
  monotone f /\ monotone g ==> monotone (f o g)
Proof
  rw[monotone_def]
QED

Theorem poset_lift:
  poset (s,r) ⇒ poset (pointwise_lift s (s,r))
Proof
  rw[poset_def, pointwise_lift_def, function_def] >-
   (qexists_tac ‘λ_. x’ >> rw[]) >-
   (cheat (* not true, can differ outside carrier. need type? *)
   ) >-
   (metis_tac[])
QED

(* general *)
Definition compatible_def:
  compatible p b f = (monotonic p b /\ monotonic p f /\
                      !x. (x IN carrier p) ==> relation p (f(b x)) (b(f x)))
End

Theorem compatible_self:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b
  ==> compatible (s,r) b b
Proof
  rw[poset_def, compatible_def, function_def, IN_DEF]
QED

Theorem compatible_id:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b
  ==> compatible (s,r) b I
Proof
  rw[compatible_def, monotonic_def, poset_def, IN_DEF]
QED

Theorem compatible_const_gfp:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  po_gfp (s,r) b fp
  ==> compatible (s,r) b (K fp)
Proof
  rw[compatible_def, monotone_def, gfp_def, poset_def, monotonic_def]
QED

(* λX. BIGUNION {f X | f | compatible b f} *)
Definition companion_def:
  companion (s,r) b t
  = !x. lub (s,r) {f x | f | compatible (s,r) b f /\ function s s f} (t x)
End

Theorem compatible_below_companion:
  poset (s,r) /\ s x /\ function s s f /\
  compatible (s,r) b f /\ companion (s,r) b t
  ==> r (f x) (t x)
Proof
  rw[companion_def] >>
  gvs[lub_def, PULL_EXISTS, function_def]
QED

(* f x <= f y <= t y is upper bound *)
Theorem companion_mono:
  poset (s,r) /\ function s s b /\ function s s t /\
  monotonic (s,r) b /\ companion (s,r) b t
  ==> monotonic (s,r) t
Proof
  rw[companion_def, lub_def, PULL_EXISTS] >>
  drule_all_then strip_assume_tac compatible_self >>
  rw[monotonic_def] >>
  first_assum $ qspec_then ‘x’ strip_assume_tac >>
  qpat_x_assum ‘!z. _ /\ compatible _ _ _ /\ _ ==> _’ kall_tac >>
  first_x_assum $ qspec_then ‘t y’ strip_assume_tac >>
  pop_assum match_mp_tac >>
  rw[function_def] >>
  (* establish fx < ty *)
  last_x_assum $ qspec_then ‘y’ strip_assume_tac >> pop_assum kall_tac >>
  pop_assum $ qspec_then ‘f’ strip_assume_tac >>
  gvs[function_def] >>
  gvs[poset_def, monotonic_def] >>
  qpat_x_assum ‘!x y z. _ ==> _’ irule >>
  rw[PULL_EXISTS] >>
  first_x_assum $ irule_at Any >>
  metis_tac[compatible_def, monotonic_def]
QED

Theorem compatible_companion:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  function s s t /\ companion (s,r) b t
  ==> compatible (s,r) b t
Proof
  rw[compatible_def] >- (metis_tac[companion_mono]) >>
  gvs[companion_def, lub_def, PULL_EXISTS, IN_DEF] >>
  first_assum $ qspec_then ‘b x’ strip_assume_tac >>
  pop_assum irule >>
  rw[] >- (fs[function_def]) >>
  ‘r (b (f x)) (b (t x))’ by gvs[monotonic_def, function_def] >>
  fs[poset_def, compatible_def, IN_DEF] >>
  first_x_assum $ qspec_then ‘x’ strip_assume_tac >>
  last_assum match_mp_tac >>
  pop_assum $ irule_at Any >>
  gvs[function_def, monotonic_def]
QED

Theorem compatible_compose:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  function s s f /\ function s s g /\
  compatible (s,r) b f /\ compatible (s,r) b g
  ==> compatible (s,r) b (f o g)
Proof
  rw[poset_def, compatible_def, monotonic_def, function_def, IN_DEF] >>
  metis_tac[]
QED

Theorem companion_gt:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  function s s t /\ companion (s,r) b t /\ s x
  ==> r x (t x)
Proof
  rpt strip_tac >>
  ho_match_mp_tac compatible_below_companion >>
  rw[function_def, compatible_companion] >>
  rw[GSYM combinTheory.I_EQ_IDABS, compatible_id]
QED

Theorem companion_idem:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  function s s t /\ companion (s,r) b t /\ s x
  ==> t (t x) = t x
Proof
  rpt strip_tac >>
  ‘r (t (t x)) (t x) /\ r (t x) (t (t x))’ suffices_by fs[poset_def, function_def] >>
  CONJ_TAC >-
   (‘compatible (s,r) b (t o t)’ by gvs[compatible_compose, compatible_companion] >>
    ho_match_mp_tac compatible_below_companion >>
    gvs[function_def] >>
    metis_tac[]) >-
   (metis_tac[companion_gt, function_def])
QED

Theorem monotonic_comp:
  monotonic (s,r) f /\ monotonic (s,r) g /\ function s s g
  ==> monotonic (s,r) (f o g)
Proof
  rw[monotonic_def, function_def]
QED

Theorem companion_bot_gfp:
  monotone b
  ==> companion b {} = gfp b
Proof
  rw[SET_EQ_SUBSET] >-
   (* t⊥ <= tb⊥ <= bt⊥ *)
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
  enhance b = b o (companion b)
End

Theorem companion_coinduct:
  monotone b
  ==> x SUBSET enhance b x
  ==> x SUBSET gfp b
Proof
  rw[enhance_def] >>
  ‘(companion b) x SUBSET gfp b’ suffices_by metis_tac[companion_gt, SUBSET_TRANS] >>
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
  ==> gfp (enhance b) = gfp b
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
  semicompatible b f = !x. f x SUBSET companion b x
End

Theorem param_coind_init:
  monotone b
  ==> {(xs,ys)} SUBSET companion b {}
  ==> (xs,ys) IN gfp b
Proof
  rw[companion_bot_gfp]
QED

Theorem param_coind_done:
  monotone b
  ==> y SUBSET x ==> y SUBSET companion b x
Proof
  metis_tac[companion_gt, SUBSET_TRANS]
QED

Theorem param_coind_upto_f:
  monotone b
  ==> y SUBSET f (companion b x) /\ semicompatible b f
  ==> y SUBSET companion b x
Proof
  rw[semicompatible_def] >>
  (* matches drule precondition against assumptions *)
  drule_then match_mp_tac SUBSET_TRANS >>
  match_mp_tac SUBSET_TRANS >>
  first_assum $ irule_at (Pos hd) >>
  simp[companion_idem]
QED

Definition wcontinuous_def:
  wcontinuous b = !P. (b (BIGINTER P) = BIGINTER { b s | s IN P })
End

Theorem continuous_mono:
  wcontinuous b ==> monotone b
Proof
  rw[wcontinuous_def, monotone_def] >>
  ‘X = BIGINTER { X; Y }’ by rw[BIGINTER_INTER, SUBSET_INTER1] >>
  ‘b (BIGINTER {X; Y}) SUBSET b Y’ suffices_by metis_tac[] >>
  pop_last_assum $ qspec_then ‘{X; Y}’ strip_assume_tac >>
  ‘BIGINTER {b s | s IN {X; Y}} SUBSET b Y’ suffices_by metis_tac[] >>
  ‘BIGINTER {b s | s IN {X; Y}} = BIGINTER {b X; b Y}’ by cheat >>
  rw[]
QED

Theorem continuous_fixpoint:
  wcontinuous b ==> gfp b = BIGINTER (λx. ?n. x = FUNPOW b n (K T))
Proof
  rw[Once SET_EQ_SUBSET] >-
   (rw[SUBSET_DEF] >>
    pop_assum mp_tac >>
    ‘gfp b SUBSET FUNPOW b n (K T)’ suffices_by metis_tac[GSYM SUBSET_DEF] >>
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
  !b. wcontinuous b
      ==> companion b = (λx. BIGINTER (λs. ?n. s = FUNPOW b n (K T) /\ x SUBSET s))
Proof
  rw[Once FUN_EQ_THM, SET_EQ_SUBSET] >-
   (rw[companion_def, SUBSET_DEF, PULL_EXISTS] >>
    subgoal ‘FUNPOW b n (f (K T)) SUBSET FUNPOW b n (K T)’ >-
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
  connection_join b g = λx. BIGUNION { f x | !y. f (b y) SUBSET b (g y) }
End

Definition pointwise_monotone_def:
  pointwise_monotone higher_functional
  = (!f g. (!x. f x SUBSET g x) ==> !x. (higher_functional f) x SUBSET (higher_functional g) x)
End

Theorem connection_join_mono:
  monotone b
  ==> pointwise_monotone (connection_join b)
Proof
  rw[monotone_def, pointwise_monotone_def] >>
  rw[connection_join, Once SUBSET_DEF, PULL_EXISTS] >>
  qexists_tac ‘f'’ >> rw[] >>
  pop_assum $ qspec_then ‘y’ strip_assume_tac >>
  ‘b (f y) SUBSET b (g y)’ suffices_by metis_tac[SUBSET_TRANS] >>
  metis_tac[]
QED

Theorem lemma6_2:
  (!x. f x SUBSET (B g) x) = (!x. f b x SUBSET b g x)
Proof
  rw[]
QED

Theorem param_coind:
  monotone b
  ==> y SUBSET b (companion b (x UNION y)) ==> y SUBSET (companion b) x
Proof

QED














(* example *)

(* TODO specialize *)

Theorem subset_poset:
  poset (UNIV, $SUBSET)
Proof
  rw[poset_def, SUBSET_ANTISYM]
QED

open llistTheory;
Definition llist_functional:
  llist_functional R = (* in the paper, llist_functional is called "b" *)
  ({[||],[||]} UNION {(x:::xs,y:::ys) | x = y /\ (xs,ys) IN R})
End

Theorem llist_inversion:
  (x, y) IN llist_functional R
  ==> (x = [||] /\ y = [||]) \/
    (?e xs ys. x = e:::xs /\ y = e:::ys /\ (xs,ys) IN R)
Proof
  rw[llist_functional]
QED

open itreeTauTheory;
Definition itree_wbisim_functional:
  itree_wbisim_functional R =
  ({ (t,t') | ?r. strip_tau t (Ret r) /\ strip_tau t' (Ret r)}
 UNION { (t,t') | ?e k k'. strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
                       !r. (k r, k' r) IN R }
 UNION { (Tau t, Tau t') | (t,t') IN R })
End

(*  llist_functional {}
      the set of all list pairs such that either:
      - they're both empty, or
      - they both have the same head
    llist_functional(llist_functional {} )
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
  ones' = LUNFOLD (λx. SOME (~x,1)) T
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
  !t t' R.
    (t,t') IN R /\
    R SUBSET itree_wbisim_functional (companion itree_wbisim_functional R)
    ==> itree_wbisim t t'
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
  compatible $ (λR. R UNION {([||],[||])} UNION {x:::xs,y:::ys | x = y /\ (xs,ys) IN R})
Proof
  rw[compatible_def,monotone_def,SUBSET_DEF,PULL_EXISTS] >>
  gvs[llist_functional]
QED

Definition cons_rel_def:
  cons_rel R = {x:::xs,y:::ys | x = y /\ (xs,ys) IN R}
End

Theorem semicompatible_cons:
  semicompatible cons_rel
Proof
  rw[semicompatible_def,SUBSET_DEF,companion_def,cons_rel_def] >>
  irule_at (Pos last) compatible_cons >>
  rw[]
QED

Theorem llist_functional_cons:
  {(x:::xs,x:::ys)} SUBSET llist_functional R
  <=> {(xs,ys)} SUBSET R
Proof
  rw[llist_functional,SUBSET_DEF]
QED

Theorem cons_rel_cons:
  {(x:::xs,x:::ys)} SUBSET cons_rel R
  <=> {(xs,ys)} SUBSET R
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
