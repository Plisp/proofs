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

(* TODO posetTheory? maybe add lub *)
Theorem po_gfp_coinduct:
  po_gfp (s,r) b gfix /\ s x /\ r x (b x)
  ==> r x gfix
Proof
  rw[gfp_def]
QED

Theorem glb_uniq:
  poset (s,r) /\
  glb (s,r) p a /\ glb (s,r) p b
  ==> a = b
Proof
  rw[glb_def] >>
  drule_then irule poset_antisym >> simp[]
QED

(* general *)

Theorem function_in:
  function s s t /\ s x ==> s (t x)
Proof
  rw[function_def]
QED

Theorem gfp_in:
  po_gfp (s,r) b gfix ==> s gfix
Proof
  rw[gfp_def]
QED

Definition lift_rel:
  lift_rel (s,r) f g = !x. s x ==> r (f x) (g x)
End

(* f (b x) steps to f x *)
Definition compatible_def:
  compatible (s,r) b f = (function s s f /\ monotonic (s,r) f /\
                          lift_rel (s,r) (f o b) (b o f))
End

Theorem compatible_self:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b
  ==> compatible (s,r) b b
Proof
  rw[poset_def, compatible_def, function_def, lift_rel]
QED

Theorem compatible_id:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b
  ==> compatible (s,r) b I
Proof
  rw[compatible_def, monotonic_def, poset_def, function_def, lift_rel]
QED

Theorem compatible_const_gfp:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  po_gfp (s,r) b fp
  ==> compatible (s,r) b (K fp)
Proof
  rw[compatible_def, monotone_def, gfp_def, poset_def, monotonic_def,
     function_def, lift_rel]
QED

(* λX. BIGUNION {f X | f | compatible b f} *)
Definition companion_def:
  companion (s,r) b t = (function s s t /\
     !x. lub (s,r) { f x | f | compatible (s,r) b f } (t x))
End

Theorem companion_unique:
  poset (s,r) ∧
  companion (s,r) b t ∧ companion (s,r) b t'
  ⇒ s x ⇒ t x = t' x
Proof
  rw[companion_def, function_def, lub_def] >>
  irule poset_antisym >>
  qexistsl_tac [‘r’, ‘s’] >> fs[]
QED

Theorem compatible_below_companion:
  poset (s,r) /\
  compatible (s,r) b f /\ companion (s,r) b t
  ==> lift_rel (s,r) f t
Proof
  rw[companion_def, lift_rel] >>
  ‘function s s f’ by fs[compatible_def] >>
  gvs[lub_def, PULL_EXISTS, function_def]
QED

(* f x <= f y <= t y is upper bound *)
Theorem companion_mono:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  companion (s,r) b t ==> monotonic (s,r) t
Proof
  rw[companion_def, lub_def, PULL_EXISTS] >>
  drule_all_then strip_assume_tac compatible_self >>
  rw[monotonic_def] >>
  first_assum $ qspec_then ‘x’ strip_assume_tac >>
  pop_assum match_mp_tac >> rw[] >>
  (* establish fx < ty *)
  last_x_assum $ qspec_then ‘y’ strip_assume_tac >> pop_assum kall_tac >>
  pop_assum $ qspec_then ‘f’ strip_assume_tac >>
  fs[compatible_def, poset_def, function_def] >>
  metis_tac[compatible_def, monotonic_def]
QED

Theorem compatible_companion:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  companion (s,r) b t ==> compatible (s,r) b t
Proof
  rw[compatible_def]
  >- (fs[companion_def])
  >- (metis_tac[companion_mono]) >>
  rw[lift_rel] >>
  gvs[companion_def, lub_def, PULL_EXISTS] >>
  first_assum $ qspec_then ‘b x’ strip_assume_tac >>
  pop_assum irule >>
  rw[function_in] >>
  fs[compatible_def] >>
  drule_then irule poset_trans >>
  rw[function_in] >>
  qexists_tac ‘b (f x)’ >>
  gvs[function_def, monotonic_def, lift_rel]
QED

Theorem compatible_compose:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  compatible (s,r) b f /\ compatible (s,r) b g
  ==> compatible (s,r) b (f o g)
Proof
  rw[poset_def, compatible_def, monotonic_def, function_def, lift_rel] >>
  metis_tac[]
QED

Theorem companion_gt:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  companion (s,r) b t /\
  s x ==> r x (t x)
Proof
  strip_tac >>
  ‘lift_rel (s,r) I t’ suffices_by rw[lift_rel] >>
  ho_match_mp_tac compatible_below_companion >>
  rw[function_def, compatible_companion] >>
  rw[GSYM combinTheory.I_EQ_IDABS, compatible_id]
QED

Theorem companion_idem:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  companion (s,r) b t /\
  s x ==> t (t x) = t x
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then irule poset_antisym >>
  rw[function_in] >-
   (‘lift_rel (s,r) (t o t) t’ suffices_by rw[lift_rel] >>
    ho_match_mp_tac compatible_below_companion >>
    rw[function_def, GSYM combinTheory.o_DEF] >>
    irule compatible_compose >>
    rw[compatible_companion]) >-
   (metis_tac[companion_def, function_def, companion_gt])
QED

Theorem monotonic_comp:
  monotonic (s,r) f /\ monotonic (s,r) g /\ function s s g
  ==> monotonic (s,r) (f o g)
Proof
  rw[monotonic_def, function_def]
QED

Theorem companion_bot_gfp:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  bottom (s,r) bot /\ po_gfp (s,r) b gfix /\
  companion (s,r) b t
  ==> t bot = gfix
Proof
  rw[] >>
  drule_then irule poset_antisym >> rw[]
  >- (fs[companion_def, function_in, bottom_def])
  >- (fs[gfp_def])
  (* t⊥ <= tb⊥ <= bt⊥ *)
  >- (match_mp_tac po_gfp_coinduct >>
      ‘function s s t’ by fs[companion_def] >>
      fs[function_in, bottom_def] >>
      drule_then match_mp_tac poset_trans >>
      qexists_tac ‘t (b bot)’ >>
      rw[bottom_def, function_in]
      >- (irule (iffLR monotonic_def) >> metis_tac[companion_mono, function_def]) >>
      ‘compatible (s,r) b t’ suffices_by fs[compatible_def, lift_rel] >>
      irule compatible_companion >> rw[])
  >- (drule_all compatible_const_gfp >> strip_tac >>
      fs[companion_def, lub_def] >>
      first_x_assum $ qspec_then ‘bot’ strip_assume_tac >>
      first_x_assum irule >>
      fs[gfp_def] >>
      qexists_tac ‘K gfix’ >> rw[function_def])
QED

(* any post fixpoint is below the greatest fixpoint *)
Theorem companion_coinduct:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  companion (s,r) b t /\
  po_gfp (s,r) b gfix /\
  s x /\ r x ((b o t) x) ==> r x gfix
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then match_mp_tac poset_trans >>
  qexists_tac ‘t x’ >> rw[function_in]
  >- (fs[gfp_def])
  >- (ho_match_mp_tac companion_gt >> rw[]) >>
  match_mp_tac po_gfp_coinduct >>
  rw[function_in] >>
  drule_all compatible_companion >> strip_tac >>
  drule_then match_mp_tac poset_trans >>
  qexists_tac ‘t (b (t x))’ >>
  reverse (rw[function_in])
  >- (fs[compatible_def, lift_rel] >>
      metis_tac[companion_idem, function_def]) >>
  metis_tac[monotonic_def, companion_mono, function_in]
QED

Theorem enhanced_gfp:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  po_gfp (s,r) b gfix /\
  companion (s,r) b t /\ po_gfp (s,r) (b o t) efix
  ==> efix = gfix
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then irule poset_antisym >> rw[]
  >- (fs[gfp_def])
  >- (fs[gfp_def])
  >- (drule_then match_mp_tac companion_coinduct >>
      qexistsl_tac [‘t’,‘b’] >>
      fs[gfp_def, poset_def]) >>
  irule po_gfp_coinduct >>
  qexistsl_tac [‘(b o t)’, ‘s’] >>
  fs[gfp_def] >>
  metis_tac[monotonic_def, function_def, companion_gt]
QED

(*
 * parameterized coinduction
 *)

Theorem param_coind_init:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  bottom (s,r) bot /\ po_gfp (s,r) b gfix /\
  companion (s,r) b t
  ==> r x (t bot) ==> r x gfix
Proof
  metis_tac[companion_bot_gfp]
QED

Theorem param_coind_done:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  companion (s,r) b t
  ==> s x /\ s y /\ r y x ==> r y (t x)
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then match_mp_tac poset_trans >>
  qexists_tac ‘x’ >> rw[function_in] >>
  metis_tac[companion_gt]
QED

Theorem param_coind_upto_f:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  companion (s,r) b t
  ==> function s s f /\ (!x. r (f x) (t x))
  ==> s x /\ s y /\ r y (f (t x))
  ==> r y (t x)
Proof
  rw[] >>
  drule_then match_mp_tac poset_trans >>
  first_x_assum $ irule_at Any >>
  ‘function s s t’ by fs[companion_def] >>
  simp[function_in] >>
  metis_tac[companion_idem]
QED

(*
 * second order companion
 *)

Definition endo_def:
  endo s f = !x. if s x then s (f x) else f x = ARB
End

Theorem endo_restrict:
  endo s f ==> function s s f
Proof
  metis_tac[endo_def, function_def]
QED

Definition endo_lift_def:
  endo_lift (s,r) = (endo s , lift_rel (s,r))
End

Theorem poset_lift:
  poset (s,r) ==> poset (endo_lift (s,r))
Proof
  rw[poset_def, endo_lift_def, lift_rel, endo_def]
  >- (qexists_tac ‘λx. if s x then x else ARB’ >> rw[])
  >- (metis_tac[])
  >- (rw[FUN_EQ_THM] >> metis_tac[])
  >- metis_tac[]
QED

(* TODO try following paper formalization *)
(* Definition connection_join: *)
(*   connection_join (s,r) b g = lub (s,r) { f x | !y. f (b y) SUBSET b (g y) } *)
(* End *)

(* Theorem connection_join_mono: *)
(*   monotone b *)
(*   ==> pointwise_monotone (connection_join b) *)
(* Proof *)
(*   rw[monotone_def, pointwise_monotone_def] >> *)
(*   rw[connection_join, Once SUBSET_DEF, PULL_EXISTS] >> *)
(*   qexists_tac ‘f'’ >> rw[] >> *)
(*   pop_assum $ qspec_then ‘y’ strip_assume_tac >> *)
(*   ‘b (f y) SUBSET b (g y)’ suffices_by metis_tac[SUBSET_TRANS] >> *)
(*   metis_tac[] *)
(* QED *)

(* Theorem lemma6_2: *)
(*   (!x. f x SUBSET (B g) x) = (!x. f b x SUBSET b g x) *)
(* Proof *)
(*   rw[] *)
(* QED *)

Theorem companion_alt:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  companion (s,r) b t /\
  s x ==> glb (s,r) { t z | z | s z /\ r x (t z) } (t x)
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  reverse (rw[glb_def, function_in]) >-
   (first_x_assum irule >>
    rw[function_in] >>
    metis_tac[companion_gt]) >>
  metis_tac[monotonic_def, function_in, companion_mono, companion_idem]
QED

Theorem companion_triv_join:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  companion (s,r) b t /\
  s x /\ s y /\ lub (s,r) { x; y } xy /\
  r (t x) (t y) ==> t xy = t y
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_all companion_alt >> rw[] >>
  ‘glb (s,r) {t z | z | s z /\ r xy (t z)} (t xy)’
    by metis_tac[lub_def,companion_alt] >>
  ‘{t z | z | s z /\ r y (t z)} = {t z | z | s z /\ r xy (t z)}’
    suffices_by metis_tac[glb_uniq] >>
  pop_assum kall_tac >> pop_assum kall_tac >>
  reverse (rw[EXTENSION, EQ_IMP_THM]) >-
   (qexists_tac ‘z’ >>
    fs[lub_def] >>
    metis_tac[poset_trans, function_in]) >>
  qexists_tac ‘z’ >>
  fs[lub_def] >>
  ‘r x (t z)’ suffices_by metis_tac[function_in] >>
  drule_then irule poset_trans >> rw[function_in] >>
  drule_all_then (irule_at (Pos (el 2))) companion_gt >> rw[function_in] >>
  drule_then irule poset_trans >> rw[function_in] >>
  first_x_assum $ irule_at (Pos (el 2)) >> rw[function_in] >>
  metis_tac[companion_idem, poset_trans, function_in, monotonic_def, companion_mono]
QED

(* total ordering required *)
Theorem param_coind:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  companion (s,r) b t /\
  (!x y. s x /\ s y ==> r (t x) (t y) \/ r (t y) (t x)) /\
  po_gfp (s,r) b gfix /\
  s x /\ s y /\
  lub (s,r) { x; y } xy
  ==> r y (b (t xy)) ==> r y (t x)
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  first_x_assum $ qspecl_then [‘x’, ‘y’] strip_assume_tac >>
  reverse (rfs[]) >-
   (metis_tac[poset_trans, function_in, companion_gt]) >>
  (* t(x\/y) = ty when tx <= ty so y <= bt(x\/y) <= bty
     ty <= tbty = b(ty) which means y <= (ty <= gfp)
     gfp <= tx <= ty <= gfp so tx = gfp
   *)
  drule_all companion_triv_join >> rw[] >>
  fs[] >> pop_assum kall_tac >>
  subgoal ‘r (t y) gfix’ >-
   (drule_then irule po_gfp_coinduct >> rw[function_in] >>
    ‘r (t y) (t (b (t y)))’
      by metis_tac[companion_mono, monotonic_def, function_in] >>
    drule_then irule poset_trans >> rw[function_in] >>
    pop_assum $ irule_at Any >> rw[function_in] >>
    ‘r (t (b (t y))) (b (t (t y)))’
      suffices_by metis_tac[poset_trans, companion_idem, function_in] >>
    drule_all compatible_companion >>
    rw[compatible_def, lift_rel] >>
    metis_tac[function_in]) >>
  (* finally y <= ty <= gfp = tx *)
  ‘t x = gfix’
    suffices_by metis_tac[companion_gt, poset_trans, function_in, gfp_in] >>
  (* XXX takes so much time to rw with gfp_in ?! *)
  drule_then irule poset_antisym >> rw[function_in] >-
   (metis_tac[gfp_in]) >-
   (metis_tac[poset_trans, function_in, gfp_in]) >>
  drule_all compatible_const_gfp >> rw[] >>
  ‘r ((K gfix) x) (t x)’ suffices_by rw[combinTheory.K_DEF] >>
  metis_tac[compatible_below_companion, lift_rel, function_in]
QED

(*
  powerset helpers
*)

Definition set_compatible_def:
  set_compatible b f = (monotone f ∧ ∀X. f (b X) ⊆ b (f X))
End

Theorem set_compatible:
  set_compatible b f ⇒ compatible (UNIV,$SUBSET) b f
Proof
  rw[set_compatible_def, compatible_def, lift_rel, function_def]
QED

Theorem set_compatible_self:
  monotone b ⇒ set_compatible b b
Proof
  rw[set_compatible_def, monotone_def]
QED

Theorem set_compatible_compose:
  monotone b ⇒
  set_compatible b f ∧ set_compatible b g
  ⇒ set_compatible b (f ∘ g)
Proof
  rw[monotone_def, set_compatible_def] >>
  metis_tac[SUBSET_DEF]
QED

Definition set_companion_def:
  set_companion b X = BIGUNION { f X | f | set_compatible b f }
End

Theorem set_companion:
  companion (UNIV,$SUBSET) b (set_companion b)
Proof
  rw[companion_def, set_companion_def, function_def] >>
  rw[lub_def, compatible_def, set_compatible_def, lift_rel, function_def] >>
  fs[SUBSET_DEF, BIGUNION, IN_DEF] >>
  metis_tac[]
QED

Theorem set_companion_coinduct:
  monotone b ∧
  X ⊆ (b ∘ set_companion b) X
  ⇒ X ⊆ gfp b
Proof
  rw[] >>
  irule companion_coinduct >>
  qexistsl_tac [‘b’, ‘UNIV’, ‘set_companion b’] >>
  rw[function_def, gfp_poset_gfp, set_companion]
QED

Theorem set_compatible_enhance:
  monotone b ∧ set_compatible b f ∧
  Y ⊆ f X
  ⇒ Y ⊆ set_companion b X
Proof
  rw[] >>
  drule_then irule SUBSET_TRANS >>
  irule (SRULE [lift_rel] compatible_below_companion) >>
  qexistsl_tac [‘b’, ‘UNIV’] >>
  rw[set_compatible, set_companion]
QED

(* to prove X is in a coinductive set from b, consider t⊥ *)
Theorem set_param_coind_init:
  monotone b ∧
  X ⊆ set_companion b ∅
  ⇒ X ⊆ gfp b
Proof
  rw[] >>
  drule_at_then Any irule param_coind_init >>
  qexistsl_tac [‘b’, ‘UNIV’] >>
  rw[bottom_def, set_companion, function_def, gfp_poset_gfp]
QED

(* pull f out of tX *)
Theorem set_param_coind_upto_f:
  monotone b ∧
  (∀X. f X ⊆ set_companion b X) ∧
  Y ⊆ f (set_companion b X)
  ⇒ Y ⊆ set_companion b X
Proof
  rw[] >>
  drule_at_then Any irule param_coind_upto_f >> rw[] >>
  qexistsl_tac [‘b’, ‘UNIV’] >>
  rw[set_companion, function_def]
QED

(* conclude: Y is a safe deduction from X *)
Theorem set_param_coind_done:
  monotone b ∧
  Y ⊆ X ⇒ Y ⊆ set_companion b X
Proof
  rw[] >>
  irule param_coind_done >> rw[] >>
  qexistsl_tac [‘b’, ‘UNIV’] >>
  rw[set_companion, function_def]
QED

(* do a deduction step, Y must step to itself or conclude with X *)
Theorem set_param_coind:
  monotone b ∧ (∀X Y. (set_companion b X) ⊆ (set_companion b Y) ∨
                      (set_companion b Y) ⊆ (set_companion b X))
  ⇒ Y ⊆ b (set_companion b (X ∪ Y))
  ⇒ Y ⊆ set_companion b X
Proof
  rw[] >>
  drule_at_then Any irule param_coind >>
  qexistsl_tac [‘gfp b’, ‘UNIV’] >>
  rw[function_def, set_companion, gfp_poset_gfp, lub_def] >>
  rw[SUBSET_UNION]
QED

(* sufficient condition for establishing the linear order on companion values,
   it's hard to state this in general since ordinals aren't supported *)
Definition wbounded_def:
  wbounded b = (gfp b = BIGINTER {FUNPOW b n UNIV | n | T})
End

Theorem llist_companion_total_order:
  monotone b ∧ wbounded b ⇒
  ∀X Y. set_companion b X ⊆ set_companion b Y ∨
        set_companion b Y ⊆ set_companion b X
Proof
  rw[wbounded_def] >>
  cheat
QED

(*
 * llist bisimulation
 *)

open llistTheory;
Definition llist_functional:
  llist_functional R = (* in the paper, llist_functional is called "b" *)
  ({[||],[||]} ∪ {(x:::xs,y:::ys) | x = y ∧ (xs,ys) ∈ R})
End

Theorem monotone_llist_functional[simp]:
  monotone llist_functional
Proof
  rw[monotone_def, llist_functional,pred_setTheory.SUBSET_DEF]
QED

Theorem test:
  wbounded llist_functional
Proof
  rw[wbounded_def, llist_functional] >>
  rw[SET_EQ_SUBSET] >-
   (rw[fixedPointTheory.gfp_def, BIGUNION_SUBSET, SUBSET_BIGINTER] >>
    Induct_on ‘n’ >> rw[] >>
    metis_tac[monotone_llist_functional, monotone_def, FUNPOW_SUC, SUBSET_TRANS]) >>
  irule gfp_coinduction >>
  rw[BIGINTER, llist_functional, SUBSET_DEF] >>
  Cases_on ‘x’ >>
  Cases_on ‘q’ >> Cases_on ‘r’ >> rw[]
  >- (pop_assum $ qspec_then ‘llist_functional UNIV’ strip_assume_tac >>
      ‘([||],h:::t) ∈ llist_functional UNIV’ by metis_tac[FUNPOW_1] >>
      fs[llist_functional])
  >- (pop_assum $ qspec_then ‘llist_functional UNIV’ strip_assume_tac >>
      ‘(h:::t,[||]) ∈ llist_functional UNIV’ by metis_tac[FUNPOW_1] >>
      fs[llist_functional])
  >- (pop_assum $ qspec_then ‘llist_functional UNIV’ strip_assume_tac >>
      fs[llist_functional] >>
      pop_assum irule >>
      qexists_tac ‘1’ >>
      rw[FUNPOW_1, llist_functional])
  >- (pop_assum $ qspec_then ‘FUNPOW llist_functional (SUC n) UNIV’
                  strip_assume_tac >>
      ‘(h:::t,h':::t') ∈ FUNPOW llist_functional (SUC n) UNIV’ by metis_tac[] >>
      fs[Once FUNPOW_SUC, llist_functional])
QED

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

Theorem llist_functional_gfp:
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

(* example *)
Definition ones_def:
  ones = LUNFOLD (K $ SOME ((),1)) ()
End

Definition ones'_def:
  ones' = LUNFOLD (K $ SOME ((),1)) ()
End

(* pretend these are the definitions: *)
Theorem ones_thm:
  ones = 1:::ones
Proof
  simp[ones_def] >> simp[Once LUNFOLD]
QED

Theorem ones'_thm:
  ones' = 1:::1:::1:::ones'
Proof
  simp[ones'_def] >> ntac 3 $ simp[Once LUNFOLD]
QED

(* standard solution: expand relation, can be large set, need to restart *)
Theorem ones_eq_ones':
  ones = ones'
Proof
  simp[Once LLIST_BISIMULATION] >>
  qexists_tac ‘CURRY {(ones,ones'); (ones,1:::ones'); (ones,1:::1:::ones')}’ >>
  rw[]
  >- (PURE_ONCE_REWRITE_TAC[ones_thm, ones'_thm] >> simp[] >>
      metis_tac[ones_thm,ones'_thm])
  >- (PURE_ONCE_REWRITE_TAC[ones_thm, ones'_thm] >> simp[] >>
      metis_tac[ones_thm])
  >- (PURE_ONCE_REWRITE_TAC[ones_thm, ones'_thm] >> simp[] >>
      metis_tac[ones_thm])
QED

Definition strong_enhance_def:
  strong_enhance R = R ∪ llist_functional R
End

Theorem strong_enhance_mono:
  monotone strong_enhance
Proof
  rw[monotone_def, strong_enhance_def] >-
   (metis_tac[SUBSET_TRANS, SUBSET_UNION]) >>
  metis_tac[SUBSET_TRANS, SUBSET_UNION, monotone_def, monotone_llist_functional]
QED

Theorem strong_enhance_compatible:
  set_compatible llist_functional strong_enhance
Proof
  rw[strong_enhance_def, set_compatible_def, strong_enhance_mono] >-
   (metis_tac[SUBSET_UNION, monotone_llist_functional, monotone_def]) >>
  metis_tac[SUBSET_UNION, monotone_llist_functional, monotone_def]
QED

Theorem singleton_subset:
  {x} ⊆ y ⇒ x ∈ y
Proof
  rw[]
QED

Theorem ones_eq_ones':
  ones = ones'
Proof
  ‘{(ones,ones')} ⊆ UNCURRY $=’ suffices_by rw[SUBSET_DEF] >>
  rewrite_tac[GSYM llist_functional_gfp] >>
  irule set_companion_coinduct >>
  (* ones = 1:1:1:ones after unfolding 3 times *)
  rw[Once ones_thm, Once ones_thm, Once ones_thm, Once ones'_thm] >>
  rw[llist_functional] >>
  irule singleton_subset >>
  irule set_compatible_enhance >> rw[] >>
  qexists_tac ‘strong_enhance ∘ strong_enhance’ >>
  rw[strong_enhance_def] >- (rw[llist_functional]) >>
  irule set_compatible_compose >>
  rw[strong_enhance_compatible]
QED

Definition cons_rel_def:
  cons_rel R = {x:::xs,y:::ys | x = y ∧ (xs,ys) ∈ R}
End

Theorem llist_functional_cons:
  {(x:::xs,x:::ys)} ⊆ llist_functional R ⇔ {(xs,ys)} ⊆ R
Proof
  rw[llist_functional, SUBSET_DEF]
QED

Theorem cons_rel_cons:
  {(x:::xs,x:::ys)} ⊆ cons_rel R ⇔ {(xs,ys)} ⊆ R
Proof
  rw[cons_rel_def, SUBSET_DEF]
QED

Theorem ones_eq_ones':
  ones = ones'
Proof
  ‘{(ones,ones')} ⊆ UNCURRY $=’ suffices_by rw[SUBSET_DEF] >>
  irule param_coind_init >>
  assume_tac (INST_TYPE [alpha |-> “:num”] llist_companion) >> rw[] >>
  first_assum $ irule_at Any >>
  qexists_tac ‘∅’ >> (* TODO make version with this proven, and no UNIV *)
  rw[monotone_llist_functional, function_def, bottom_def,
     llist_functional_correct, llist_functional] >>

  irule singleton_subset >>
  irule param_coind >>
  first_assum $ irule_at Any >>
  qexistsl_tac [‘{(ones,ones')}’, ‘UNCURRY $=’] >>
  simp[monotone_llist_functional, llist_functional_correct, function_def] >>
  reverse conj_tac >- (rw[lub_def] >> fs[SUBSET_DEF]) >>
  rw[Once ones'_thm, Once ones_thm, Once ones_thm, llist_functional_cons] >>
  rw[llist_functional] >>

  irule singleton_subset >>
  irule param_coind_upto_f >>
  first_assum $ irule_at Any >>
  rw[monotone_llist_functional, function_def] >>
  qexists_tac ‘cons_rel’ >>
  conj_tac >-
   cheat >>

  irule singleton_subset >>
  rw[cons_rel_cons] >>
  irule singleton_subset >>
  drule_at_then Any irule param_coind_done >>
  rw[monotone_llist_functional, function_def]
QED

(* open itreeTauTheory; *)
(* Definition itree_wbisim_functional: *)
(*   itree_wbisim_functional R = *)
(*   ({ (t,t') | ?r. strip_tau t (Ret r) /\ strip_tau t' (Ret r)} *)
(*  UNION { (t,t') | ?e k k'. strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\ *)
(*                        !r. (k r, k' r) IN R } *)
(*  UNION { (Tau t, Tau t') | (t,t') IN R }) *)
(* End *)

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
