open arithmeticTheory;
open pred_setTheory;
open fixedPointTheory;
open posetTheory;

val _ = new_theory "upto";

Theorem glb_unique:
  poset (s,r) ∧
  glb (s,r) P x ∧ glb (s,r) P y
  ⇒ x = y
Proof
  rw[glb_def] >>
  drule_then irule poset_antisym >> simp[]
QED

Theorem lub_unique:
  poset (s,r) ∧
  lub (s,r) P x ∧ lub (s,r) P y
  ⇒ x = y
Proof
  rw[lub_def] >>
  drule_then irule poset_antisym >> simp[]
QED

Theorem lub_is_gfp:
  poset (s,r) ∧ function s s f ∧ monotonic (s,r) f ∧
  lub (s,r) { x | r x (f x) } l
  ⇒ gfp (s,r) f l
Proof
  rw[lub_def, gfp_def, monotonic_def, function_def] >>
  subgoal ‘r l (f l)’ >-
   (first_x_assum irule >> rw[] >>
    drule_then irule poset_trans >>
    first_assum $ irule_at Any >> rw[]) >>
  drule_then irule poset_antisym >> rw[]
QED

(* core *)

Definition lift_rel:
  lift_rel (s,r) f g = ∀x. s x ⇒ r (f x) (g x)
End

(* f (b x) steps to f x *)
Definition compatible_def:
  compatible (s,r) b f = (function s s f ∧ monotonic (s,r) f ∧
                          lift_rel (s,r) (f ∘ b) (b ∘ f))
End

Theorem compatible_self:
  poset (s,r) ∧ function s s b ∧ monotonic (s,r) b
  ⇒ compatible (s,r) b b
Proof
  rw[poset_def, compatible_def, function_def, lift_rel]
QED

Theorem compatible_id:
  poset (s,r) ∧ function s s b ∧ monotonic (s,r) b
  ⇒ compatible (s,r) b I
Proof
  rw[compatible_def, monotonic_def, poset_def, function_def, lift_rel]
QED

Theorem compatible_const_gfp:
  poset (s,r) ∧ function s s b ∧ monotonic (s,r) b ∧
  gfp (s,r) b fp
  ⇒ compatible (s,r) b (K fp)
Proof
  rw[compatible_def, gfp_def, poset_def, monotonic_def,
     function_def, lift_rel]
QED

(* λX. BIGUNION {f X | f | compatible b f} *)
Definition companion_def:
  companion (s,r) b t = (function s s t ∧
     ∀x. lub (s,r) { f x | f | compatible (s,r) b f } (t x))
End

Theorem compatible_below_companion:
  poset (s,r) ∧
  compatible (s,r) b f ∧ companion (s,r) b t
  ⇒ lift_rel (s,r) f t
Proof
  rw[companion_def, lift_rel] >>
  ‘function s s f’ by fs[compatible_def] >>
  gvs[lub_def, PULL_EXISTS, function_def]
QED

(* f x ≤ f y ≤ t y is upper bound, compatible f must be mono *)
Theorem companion_mono:
  poset (s,r) ∧ function s s b ∧ monotonic (s,r) b ∧
  companion (s,r) b t ⇒ monotonic (s,r) t
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
  poset (s,r) ∧ function s s b ∧ monotonic (s,r) b ∧
  companion (s,r) b t ⇒ compatible (s,r) b t
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
  poset (s,r) ∧ function s s b ∧ monotonic (s,r) b ∧
  compatible (s,r) b f ∧ compatible (s,r) b g
  ⇒ compatible (s,r) b (f ∘ g)
Proof
  rw[compatible_def, lift_rel] >-
   (fs[function_def]) >-
   (fs[function_in, monotonic_def]) >>
  ‘r (f (g (b x))) (f (b (g x)))’ by metis_tac[monotonic_def, function_in] >>
  drule_then irule poset_trans >> rw[function_in] >>
  metis_tac[function_in]
QED

Theorem companion_expansive:
  poset (s,r) ∧ function s s b ∧ monotonic (s,r) b ∧
  companion (s,r) b t ∧
  s x ⇒ r x (t x)
Proof
  strip_tac >>
  ‘lift_rel (s,r) I t’ suffices_by rw[lift_rel] >>
  ho_match_mp_tac compatible_below_companion >>
  rw[function_def, compatible_companion] >>
  rw[GSYM combinTheory.I_EQ_IDABS, compatible_id]
QED

Theorem companion_idem:
  poset (s,r) ∧ function s s b ∧ monotonic (s,r) b ∧
  companion (s,r) b t ∧
  s x ⇒ t (t x) = t x
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then irule poset_antisym >>
  rw[function_in] >-
   (‘lift_rel (s,r) (t ∘ t) t’ suffices_by rw[lift_rel] >>
    ho_match_mp_tac compatible_below_companion >>
    rw[function_def, GSYM combinTheory.o_DEF] >>
    irule compatible_compose >>
    rw[compatible_companion]) >-
   (metis_tac[companion_def, function_def, companion_expansive])
QED

Theorem companion_bot_gfp:
  poset (s,r) ∧ monotonic (s,r) b ∧ function s s b ∧
  bottom (s,r) bot ∧ gfp (s,r) b gfix ∧
  companion (s,r) b t
  ⇒ t bot = gfix
Proof
  rw[] >>
  drule_then irule poset_antisym >> rw[]
  >- (fs[companion_def, function_in, bottom_def])
  >- (fs[gfp_def])
  (* t⊥ ≤ tb⊥ ≤ bt⊥ *)
  >- (match_mp_tac gfp_coinduct >>
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
  poset (s,r) ∧ monotonic (s,r) b ∧ function s s b ∧
  companion (s,r) b t ∧
  gfp (s,r) b gfix ∧
  s x ∧ r x ((b ∘ t) x) ⇒ r x gfix
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then match_mp_tac poset_trans >>
  qexists_tac ‘t x’ >> rw[function_in]
  >- (fs[gfp_def])
  >- (ho_match_mp_tac companion_expansive >> rw[]) >>
  match_mp_tac gfp_coinduct >>
  rw[function_in] >>
  drule_all compatible_companion >> strip_tac >>
  drule_then match_mp_tac poset_trans >>
  qexists_tac ‘t (b (t x))’ >>
  reverse (rw[function_in])
  >- (fs[compatible_def, lift_rel] >>
      metis_tac[companion_idem, function_def]) >>
  metis_tac[monotonic_def, companion_mono, function_in]
QED

Theorem lt_gfp_companion:
  poset (s,r) ∧ bottom (s,r) bot ∧
  function s s b ∧ monotonic (s,r) b ∧
  gfp (s,r) b fp ∧
  companion (s,r) b t ∧
  s x ∧ r x fp
  ⇒ t x = fp
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_all companion_bot_gfp >> rw[] >>
  drule_all compatible_const_gfp >> rw[] >>
  drule_then irule poset_antisym >> fs[function_in] >>
  rw[] >-
   (fs[function_in, bottom_def]) >-
   (‘r (t x) (t (t bot))’ by metis_tac[companion_mono, monotonic_def,
                                       function_in, bottom_def] >>
    metis_tac[companion_idem, poset_trans, function_in, bottom_def]) >>
  ‘r ((K (t bot)) x) (t x)’ suffices_by rw[] >>
  metis_tac[compatible_below_companion, compatible_const_gfp, lift_rel, function_in]
QED

Theorem enhanced_gfp:
  poset (s,r) ∧ monotonic (s,r) b ∧ function s s b ∧
  gfp (s,r) b gfix ∧
  companion (s,r) b t ∧ gfp (s,r) (b ∘ t) efix
  ⇒ efix = gfix
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then irule poset_antisym >> rw[]
  >- (fs[gfp_def])
  >- (fs[gfp_def])
  >- (drule_then match_mp_tac companion_coinduct >>
      qexistsl_tac [‘t’,‘b’] >>
      fs[gfp_def, poset_def]) >>
  irule gfp_coinduct >>
  qexistsl_tac [‘(b ∘ t)’, ‘s’] >>
  fs[gfp_def] >>
  metis_tac[monotonic_def, function_def, companion_expansive]
QED

(*
 * parameterized coinduction
 *)

Theorem param_coind_init:
  poset (s,r) ∧ monotonic (s,r) b ∧ function s s b ∧
  bottom (s,r) bot ∧ gfp (s,r) b gfix ∧
  companion (s,r) b t
  ⇒ r x (t bot) ⇒ r x gfix
Proof
  metis_tac[companion_bot_gfp]
QED

Theorem param_coind_done:
  poset (s,r) ∧ monotonic (s,r) b ∧ function s s b ∧
  companion (s,r) b t
  ⇒ s x ∧ s y ∧ r y x ⇒ r y (t x)
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then match_mp_tac poset_trans >>
  qexists_tac ‘x’ >> rw[function_in] >>
  metis_tac[companion_expansive]
QED

Theorem param_coind_upto_f:
  poset (s,r) ∧ monotonic (s,r) b ∧ function s s b ∧
  companion (s,r) b t
  ⇒ function s s f ∧ (∀x. r (f x) (t x))
  ⇒ s x ∧ s y ∧ r y (f (t x))
  ⇒ r y (t x)
Proof
  rw[] >>
  drule_then match_mp_tac poset_trans >>
  first_x_assum $ irule_at Any >>
  ‘function s s t’ by fs[companion_def] >>
  simp[function_in] >>
  metis_tac[companion_idem]
QED

(*
 * parameterized coinduction via ordering
 *)

Theorem companion_alt:
  poset (s,r) ∧ monotonic (s,r) b ∧ function s s b ∧
  companion (s,r) b t ∧
  s x ⇒ glb (s,r) { t z | z | s z ∧ r x (t z) } (t x)
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  reverse (rw[glb_def, function_in]) >-
   (first_x_assum irule >>
    rw[function_in] >>
    metis_tac[companion_expansive]) >>
  metis_tac[monotonic_def, function_in, companion_mono, companion_idem]
QED

Theorem companion_triv_join:
  poset (s,r) ∧ monotonic (s,r) b ∧ function s s b ∧
  companion (s,r) b t ∧
  s x ∧ s y ∧ lub (s,r) { x; y } xy ∧
  r (t x) (t y) ⇒ t xy = t y
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_all companion_alt >> rw[] >>
  ‘glb (s,r) {t z | z | s z ∧ r xy (t z)} (t xy)’
    by metis_tac[lub_def,companion_alt] >>
  ‘{t z | z | s z ∧ r y (t z)} = {t z | z | s z ∧ r xy (t z)}’
    suffices_by metis_tac[glb_unique] >>
  pop_assum kall_tac >> pop_assum kall_tac >>
  reverse (rw[EXTENSION, EQ_IMP_THM]) >-
   (qexists_tac ‘z’ >>
    fs[lub_def] >>
    metis_tac[poset_trans, function_in]) >>
  qexists_tac ‘z’ >>
  fs[lub_def] >>
  ‘r x (t z)’ suffices_by metis_tac[function_in] >>
  drule_then irule poset_trans >> rw[function_in] >>
  drule_all_then (irule_at (Pos (el 2))) companion_expansive >> rw[function_in] >>
  drule_then irule poset_trans >> rw[function_in] >>
  first_x_assum $ irule_at (Pos (el 2)) >> rw[function_in] >>
  ‘r (t y) (t (t z))’ by metis_tac[companion_mono, monotonic_def, function_in] >>
  metis_tac[companion_idem, poset_trans, function_in]
QED

(* total ordering required *)
Theorem param_coind':
  poset (s,r) ∧ monotonic (s,r) b ∧ function s s b ∧
  companion (s,r) b t ∧
  (∀x y. s x ∧ s y ⇒ r (t x) (t y) ∨ r (t y) (t x)) ∧
  gfp (s,r) b gfix ∧
  s x ∧ s y ∧
  lub (s,r) { x; y } xy
  ⇒ r y (b (t xy)) ⇒ r y (t x)
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  first_x_assum $ qspecl_then [‘x’, ‘y’] strip_assume_tac >>
  reverse (rfs[]) >-
   (metis_tac[poset_trans, function_in, companion_expansive]) >>
  (* t(x∨y) = ty when tx ≤ ty so y ≤ bt(x∨y) ≤ bty
     ty ≤ tbty = b(ty) which means y ≤ (ty ≤ gfp)
     gfp ≤ tx ≤ ty ≤ gfp so tx = gfp
   *)
  drule_all companion_triv_join >> rw[] >>
  fs[] >> pop_assum kall_tac >>
  subgoal ‘r (t y) gfix’ >-
   (drule_then irule gfp_coinduct >> rw[function_in] >>
    ‘r (t y) (t (b (t y)))’
      by metis_tac[companion_mono, monotonic_def, function_in] >>
    drule_then irule poset_trans >> rw[function_in] >>
    pop_assum $ irule_at Any >> rw[function_in] >>
    ‘r (t (b (t y))) (b (t (t y)))’
      suffices_by metis_tac[poset_trans, companion_idem, function_in] >>
    drule_all compatible_companion >>
    rw[compatible_def, lift_rel] >>
    metis_tac[function_in]) >>
  (* finally y ≤ ty ≤ gfp = tx *)
  ‘s gfix’ by fs[gfp_def] >>
  ‘t x = gfix’
    suffices_by metis_tac[companion_expansive, poset_trans, function_in] >>
  drule_then irule poset_antisym >> rw[function_in] >-
   (metis_tac[poset_trans, function_in]) >>
  drule_all compatible_const_gfp >> rw[] >>
  ‘r ((K gfix) x) (t x)’ suffices_by rw[combinTheory.K_DEF] >>
  metis_tac[compatible_below_companion, lift_rel, function_in]
QED

(*
 * parameterized formalization following the cawu paper with 2nd order lattice
 *)

Definition endo_def:
  endo (s,r) f = (monotonic (s,r) f ∧ ∀x. if s x then s (f x) else f x = @y. ¬s y)
End

Definition endo_lift_def:
  endo_lift (s,r) = (endo (s,r) , lift_rel (s,r))
End

Theorem endo_in:
  endo (s,r) t ∧ s x ⇒ s (t x)
Proof
  rw[endo_def] >> metis_tac[]
QED

(* this is one reason why we need choose instead of ARB (which can be in s) *)
Theorem endo_comp:
  endo (s,r) f ∧ endo (s,r) g ⇒ endo (s,r) (f ∘ g)
Proof
  rw[endo_def] >-
   (metis_tac[monotonic_comp, function_def]) >>
  rw[] >> metis_tac[]
QED

Theorem endo_poset:
  poset (s,r) ⇒ poset (endo_lift (s,r))
Proof
  rw[poset_def, endo_lift_def, lift_rel, endo_def]
  >- (qexists_tac ‘λx. if s x then x else @y. ¬s y’ >> rw[monotonic_def])
  >- (metis_tac[])
  >- (rw[FUN_EQ_THM] >> metis_tac[])
  >- (metis_tac[])
QED

(* what join functionals B are impredicative?
 * Bg = ⋁ f | P(f) where P(Bg)
 *
 * for P = - ∘ p ≤ Rg,
 * h < Bg ⇒ hp ≤ (Bg)p ≤ Rg, since all f in Bg have f(p x) ≤ Rg
 * so all (Bg ∘ p)x = Bg(p x) ≤ Rg
 *)

Definition B_join_def:
  B_join (s,r) b B =
  (function (endo (s,r)) (endo (s,r)) B ∧ monotonic (endo_lift (s,r)) B ∧
   ∀g x. lub (s,r) { f x | f | endo (s,r) f ∧ lift_rel (s,r) (f ∘ b) (b ∘ g) }
             (B g x))
End

Theorem compatible_B_functional_postfix:
  poset (s,r) ∧ endo (s,r) b ∧
  B_join (s,r) b B ∧
  endo (s,r) f ⇒
  (lift_rel (s,r) f (B f) ⇔ lift_rel (s,r) (f ∘ b) (b ∘ f))
Proof
  reverse (rw[B_join_def, EQ_IMP_THM]) >-
   (fs[lub_def, lift_rel] >> metis_tac[endo_in]) >>
  (* look pointwise since the predicate is pointwise *)
  subgoal ‘lift_rel (s,r) (B f ∘ b) (b ∘ f)’ >-
   (fs[lub_def] >> rw[lift_rel] >>
    first_x_assum $ qspecl_then [‘f’, ‘b x’] strip_assume_tac >>
    first_x_assum irule >> rw[SF SFY_ss, endo_in] >>
    fs[lift_rel]) >>
  fs[lift_rel] >> rw[endo_in] >>
  drule_then irule poset_trans >> rw[SF SFY_ss, endo_in] >>
  fs[endo_lift_def] >>
  metis_tac[endo_in, monotonic_def, function_def]
QED

Theorem endo_function:
  endo (s,r) f ⇒ function s s f
Proof
  metis_tac[endo_def, function_def]
QED

Theorem B_greatest_fixpoint_is_companion:
  poset (s,r) ∧ endo (s,r) b ∧
  endo (s,r) t ∧ companion (s,r) b t ∧
  B_join (s,r) b B
  ⇒ gfp (endo_lift (s,r)) B t
Proof
  rw[EQ_IMP_THM] >>
  drule endo_poset >> rw[] >>
  fs[endo_lift_def] >>
  qabbrev_tac ‘t' = (λx. if s x then t x else @y. ¬s y)’ >>
  subgoal ‘lub (endo (s,r),lift_rel (s,r)) {f | lift_rel (s,r) f (B f)} t'’ >-
   (‘endo (s,r) t'’
      by fs[Abbr ‘t'’, endo_def, monotonic_def, companion_def, function_def] >>
    ‘compatible (s,r) b t’ by
      metis_tac[compatible_companion, function_def, endo_def] >>
     fs[companion_def, lub_def] >> rw[] >-
     (rw[lift_rel] >>
      last_x_assum $ qspec_then ‘x’ strip_assume_tac >>
      fs[Abbr ‘t'’] >>
      first_x_assum irule >> rw[SF SFY_ss, endo_in] >>
      qexists_tac ‘y’ >> rw[compatible_def] >-
       (metis_tac[endo_in, function_def]) >-
       (fs[endo_def]) >>
      metis_tac[compatible_B_functional_postfix]) >>
    pop_assum irule >> rw[] >>
    ‘lift_rel (s,r) (t' ∘ b) (b ∘ t')’
      suffices_by metis_tac[compatible_B_functional_postfix] >>
    fs[compatible_def, lift_rel, Abbr ‘t'’] >>
    rw[] >>
    metis_tac[endo_in]) >>
  subgoal ‘lift_rel (s,r) (t' ∘ b) (b ∘ t')’ >-
   (drule_then irule (iffLR compatible_B_functional_postfix) >>
    fs[lub_def] >>
    qexists_tac ‘B’ >> rw[] >>
    first_x_assum irule >>
    reverse conj_tac >- (fs[B_join_def, function_def, endo_lift_def]) >>
    rw[] >>
    fs[B_join_def, endo_lift_def] >>
    ‘lift_rel (s,r) y t'’ by metis_tac[] >>
    drule_then irule poset_trans >>
    fs[function_def] >>
    qexists_tac ‘B y’ >> rw[] >>
    ‘monotonic (endo (s,r),lift_rel (s,r)) B’ by fs[endo_def] >>
    fs[monotonic_def]) >>
  subgoal ‘compatible (s,r) b t’ >-
   (drule_then irule compatible_companion >>
    fs[endo_def, function_def] >> metis_tac[]) >>
  drule_all compatible_B_functional_postfix >> rw[] >>
  (* argument: gfp B = lub of postfix points = lub of compat functions *)
  irule lub_is_gfp >> rw[] >-
   (metis_tac[endo_def, function_def, B_join_def, endo_lift_def]) >-
   (fs[B_join_def, endo_lift_def, endo_def]) >>
  ‘t = t'’ suffices_by metis_tac[] >>
  drule_then irule poset_antisym >>
  fs[B_join_def, companion_def, lub_def] >>
  rw[] >-
   (last_x_assum $ drule_then irule >> fs[compatible_def]) >>
  rw[lift_rel] >>
  last_x_assum $ qspec_then ‘x’ strip_assume_tac >>
  first_x_assum irule >>
  rw[SF SFY_ss, endo_in] >>
  qexists_tac ‘t'’ >>
  fs[compatible_def, SF SFY_ss, endo_function, endo_def]
QED

Theorem t_below_Tf:
  poset (s,r) ∧ endo (s,r) b ∧
  endo (s,r) t ∧ companion (s,r) b t ∧
  B_join (s,r) b B ∧
  bottom (endo_lift (s,r)) bot ∧
  companion (endo_lift (s,r)) B T' ∧
  endo (s,r) f
  ⇒ lift_rel (s,r) t (T' f)
Proof
  rw[] >>
  drule endo_poset >>
  drule_all B_greatest_fixpoint_is_companion >> rw[] >>
  fs[endo_lift_def] >>
  subgoal ‘T' bot = t’ >-
   (irule companion_bot_gfp >>
    qexistsl_tac [‘B’, ‘lift_rel (s,r)’, ‘endo (s,r)’] >>
    fs[SRULE [endo_lift_def] endo_poset, B_join_def, endo_lift_def]) >>
  subgoal ‘monotonic (endo (s,r),lift_rel (s,r)) T'’ >-
   (irule companion_mono >> fs[function_def] >>
    qexists_tac ‘B’ >> fs[B_join_def, endo_lift_def, function_def]) >>
  fs[monotonic_def] >>
  metis_tac[bottom_def]
QED

Theorem lift_rel_comp:
  poset (s,r) ∧
  function s s g ∧ function s s f ∧ function s s f' ∧ function s s g' ∧
  monotonic (s,r) f ∧ monotonic (s,r) f' ∧
  lift_rel (s,r) f f' ∧ lift_rel (s,r) g g'
  ⇒ lift_rel (s,r) (f ∘ g) (f' ∘ g')
Proof
  rw[lift_rel, function_def] >>
  drule_then irule poset_trans >> rw[] >>
  metis_tac[monotonic_def, poset_trans]
QED

Theorem Bf_compatible_f:
  poset (s,r) ∧ endo (s,r) b ∧ endo (s,r) f ∧
  B_join (s,r) b B
  ⇒ lift_rel (s,r) (B f ∘ b) (b ∘ f)
Proof
  rw[B_join_def, endo_lift_def, lift_rel, lub_def] >>
  first_x_assum $ qspecl_then [‘f’, ‘b x’] strip_assume_tac >>
  pop_assum irule >> pop_assum kall_tac >> rw[] >>
  metis_tac[endo_in]
QED

Theorem doubling_compatible_B:
  poset (s,r) ∧ endo (s,r) b ∧
  B_join (s,r) b B
  ⇒ compatible (endo_lift (s,r)) B (λf. f ∘ f)
Proof
  rw[compatible_def, endo_lift_def] >-
   (rw[function_def, endo_def] >-
     (irule monotonic_comp >> metis_tac[function_def]) >- (metis_tac[])) >-
   (fs[monotonic_def, B_join_def, endo_lift_def] >> rw[] >>
    metis_tac[lift_rel_comp, endo_def, function_def]) >>
  rw[lift_rel] >>
  rename1 ‘r (B f (B f y)) _’ >>
  drule_all Bf_compatible_f >> rw[] >>
  fs[lift_rel, B_join_def, endo_lift_def, lub_def] >> rw[] >>
  first_x_assum $ qspecl_then [‘f ∘ f’, ‘y’] strip_assume_tac >>
  first_x_assum irule >> pop_assum kall_tac >> rw[] >-
   (metis_tac[function_def, endo_def]) >>
  qexists_tac ‘B f ∘ B f’ >> rw[] >-
   (metis_tac[function_def, endo_comp]) >>
  drule_then irule poset_trans >> rw[] >-
   (metis_tac[endo_in, function_in]) >- (metis_tac[endo_in]) >>
  qexists_tac ‘B f (b (f x))’ >> rw[] >- (metis_tac[endo_in, function_in]) >-
   (‘monotonic (s,r) (B f)’ by metis_tac[function_def, endo_def] >>
    fs[monotonic_def] >> metis_tac[endo_def, function_def]) >>
  metis_tac[endo_def, function_def]
QED

Theorem Tf_idem:
  poset (s,r) ∧ endo (s,r) b ∧
  B_join (s,r) b B ∧
  endo (s,r) t ∧ companion (s,r) b t ∧
  companion (endo_lift (s,r)) B T' ∧
  bottom (endo_lift (s,r)) bot ∧
  endo (s,r) f
  ⇒ T' f ∘ T' f = T' f
Proof
  rw[endo_lift_def] >>
  drule endo_poset >> rw[] >>
  irule poset_antisym >>
  qexistsl_tac [‘lift_rel (s,r)’, ‘endo (s,r)’] >> rw[] >-
   (metis_tac[companion_def, function_def, endo_comp, endo_def]) >-
   (metis_tac[companion_def, function_def, endo_comp, endo_def]) >-
   (fs[endo_lift_def])
  >- (irule poset_trans >>
      qexistsl_tac [‘endo (s,r)’, ‘T' (T' f)’] >>
      fs[B_join_def, endo_lift_def, function_def] >>
      rw[] >-
       (metis_tac[endo_comp, companion_def, function_def]) >-
       (metis_tac[companion_def, function_def]) >-
       (metis_tac[companion_def, function_def]) >-
       (‘lift_rel (endo (s,r),lift_rel (s,r)) ((λf. f ∘ f) ∘ T') (T' ∘ T')’
          suffices_by fs[lift_rel] >>
        irule lift_rel_comp >> fs[] >>
        ‘function (endo (s,r)) (endo (s,r)) T'’ by metis_tac[companion_def] >>
        rw[] >-
         (rw[monotonic_def] >>
          irule lift_rel_comp >> metis_tac[endo_def, function_def]) >-
         (irule companion_mono >> metis_tac[function_def]) >-
         (rw[function_def, endo_comp]) >-
         (irule compatible_below_companion >> rw[] >>
          qexists_tac ‘B’ >> rw[GSYM endo_lift_def] >>
          irule doubling_compatible_B >>
          rw[B_join_def, endo_lift_def] >> metis_tac[function_def]) >-
         (rw[lift_rel] >> metis_tac[poset_refl, endo_in, function_def])) >-
       (‘T' (T' f) = T' f’
          suffices_by metis_tac[poset_refl, companion_def, function_def] >>
        irule companion_idem >>
        qexistsl_tac [‘B’, ‘lift_rel (s,r)’, ‘endo (s,r)’] >>
        metis_tac[function_def, endo_def])) >>
  (* Tf∘id ≤ Tf∘t ≤ Tf∘Tf *)
  ‘lift_rel (s,r) (T' f ∘ I) (T' f ∘ T' f)’ suffices_by rw[] >>
  irule lift_rel_comp >>
  ‘function s s (T' f)’ by metis_tac[function_def, companion_def, endo_def] >>
  ‘monotonic (s,r) (T' f)’ by metis_tac[function_def, companion_def, endo_def] >>
  rw[] >-
   (fs[function_def]) >-
   (rw[lift_rel] >> metis_tac[poset_refl, companion_def, function_def, endo_def]) >-
   (drule_all (SRULE [endo_lift_def] t_below_Tf) >>
    rw[lift_rel] >>
    drule_then irule poset_trans >> rw[] >-
     (metis_tac[companion_def, function_def, endo_def]) >>
    qexists_tac ‘t x’ >> rw[SF SFY_ss, endo_in] >>
    drule_then irule companion_expansive >>
    metis_tac[function_def, endo_def])
QED

(* only needs finite lubs aside from t, B and T, completeness is just convenient
   maybe somehow B_join and the higher companion forces the boundedness∃
 *)
Theorem param_coind:
  poset (s,r) ∧ complete (s,r) ∧ endo (s,r) b ∧
  companion (s,r) b t ∧ endo (s,r) t ∧
  B_join (s,r) b B ∧ companion (endo_lift (s,r)) B T' ∧
  gfp (s,r) b gfix ∧
  s x ∧ s y ∧
  lub (s,r) { x; y } xy
  ⇒ r y (b (t xy)) ⇒ r y (t x)
Proof
  rw[] >>
  ‘monotonic (s,r) t’ by metis_tac[companion_mono, lub_def, endo_def] >>
  ‘monotonic (s,r) b’ by metis_tac[function_def, endo_def] >>
  ‘∃bot. lub (s,r) ∅ bot’ by metis_tac[complete_def] >>
  reverse (subgoal ‘lift_rel (s,r)
                    (λz. if s z then (if r x z then y else bot) else @y. ¬s y)
                    t’) >-
   (fs[lift_rel] >>
    pop_assum $ qspec_then ‘x’ strip_assume_tac >>
    Cases_on ‘r x x’ >> metis_tac[poset_refl]) >>
  qmatch_goalsub_abbrev_tac ‘lift_rel _ f _’ >>
  subgoal ‘endo (s,r) f’ >-
   (rw[endo_def, Abbr ‘f’] >-
     (rw[monotonic_def] >>
      Cases_on ‘r x z’ >-
       (metis_tac[poset_refl, poset_trans]) >>
      fs[lub_def] >> metis_tac[]) >>
    Cases_on ‘r x z’ >> fs[lub_def] >> metis_tac[]) >>
  drule_all B_greatest_fixpoint_is_companion >>
  rw[endo_lift_def] >>
  irule companion_coinduct >>
  qexistsl_tac [‘B’, ‘endo (s,r)’, ‘T'’] >> rw[] >-
   (* begin *)
   (metis_tac[endo_poset, endo_lift_def]) >-
   (‘∃fxl. lub (s,r) { f x ; x } fxl’ by metis_tac[complete_def] >>
    subgoal ‘xy = fxl’ >-
     (drule_then irule lub_unique >>
      ‘y = f x’ by metis_tac[Abbr ‘f’, poset_refl] >> fs[] >>
      ‘{x; f x} = {f x; x}’ by rw[SET_EQ_SUBSET, SUBSET_DEF] >>
      fs[] >> metis_tac[]) >>
    drule_then strip_assume_tac (iffLR B_join_def) >>
    fs[endo_lift_def] >>
    rw[lift_rel] >>
    last_x_assum $ qspecl_then [‘T' f’, ‘x'’] strip_assume_tac >>
    pop_assum mp_tac >>
    rw[lub_def] >>
    first_x_assum irule >> pop_assum kall_tac >>
    conj_tac >- (fs[Abbr ‘f’] >> Cases_on ‘r x x'’ >> fs[lub_def]) >>
    qexists_tac ‘f’ >> rw[] >> ntac 2 (pop_assum kall_tac) >>
    rw[lift_rel] >>
    reverse (Cases_on ‘r x (b x')’) >-
     (reverse (rw[Abbr ‘f’, endo_in]) >- (metis_tac[endo_in]) >>
      fs[lub_def] >>
      ‘s (T' (λz. if s z then if r x z then y else bot else @y. ¬s y) x')’
        suffices_by metis_tac[endo_in] >>
      fs[companion_def] >>
      metis_tac[function_def, endo_in]) >>
    subgoal ‘f (b x') = y’ >- (fs[Abbr ‘f’] >> metis_tac[endo_in]) >>
    rfs[] >> pop_assum kall_tac >>
    drule_then irule poset_trans >>
    ‘s (b (T' f x'))’ by metis_tac[endo_in, companion_def, function_def] >>
    rw[] >>
    qexists_tac ‘b (t fxl)’ >> rw[endo_in] >- (metis_tac[lub_def, endo_in]) >>
    drule_then irule poset_trans >> rw[] >- (metis_tac[lub_def, endo_in]) >>
    ‘∃fbxl. lub (s,r) { f (b x') ; b x' } fbxl’ by metis_tac[complete_def] >>
    qexists_tac ‘b (t fbxl)’ >> rw[] >-
     (* cases *)
     (metis_tac[endo_in, lub_def]) >-
     (‘r (t fxl) (t fbxl)’ suffices_by metis_tac[monotonic_def, lub_def,
                                                 endo_def, endo_in] >>
      ‘r fxl fbxl’ suffices_by metis_tac[companion_mono, monotonic_def, lub_def,
                                         function_def, endo_def] >>
      fs[lub_def] >>
      last_x_assum irule >> rw[] >-
       (‘r (b x') fbxl’ by metis_tac[endo_in] >>
        drule_then irule poset_trans >>
        pop_assum $ irule_at Any >>
        metis_tac[endo_in]) >-
       (‘y = f x’ by metis_tac[Abbr ‘f’, poset_refl] >> fs[] >>
        ‘r (f (b x')) fbxl’ by metis_tac[endo_in] >>
        ‘monotonic (s,r) f’ by fs[endo_def] >>
        metis_tac[monotonic_def, poset_trans, endo_in])) >>
    subgoal ‘∃fbl. ∀X. lub (s,r) { f (b X) ; b X } (fbl X)’ >-
     (rw[GSYM SKOLEM_THM] >> metis_tac[complete_def]) >>
    ‘fbxl = fbl x'’ by metis_tac[lub_unique] >> fs[] >>
    ‘r (t (fbl x')) (T' f x')’ suffices_by metis_tac[monotonic_def, lub_def,
                                                     endo_def, endo_in] >>
    ‘lift_rel (s,r) (t ∘ fbl) (T' f)’ suffices_by
      metis_tac[combinTheory.o_DEF, lift_rel] >>
    subgoal ‘bottom (endo_lift (s,r)) (λx. if s x then bot else @y. ¬s y)’ >-
     (rw[bottom_def, endo_lift_def] >-
       (rw[endo_def, monotonic_def] >-
          (metis_tac[poset_refl, lub_def]) >-
          (metis_tac[lub_def])) >-
        (rw[lift_rel, lub_def] >>
         fs[lub_def] >> metis_tac[endo_def])) >>
    subgoal ‘T' f ∘ T' f = T' f’ >-
     (drule_then irule Tf_idem >> rw[] >- (metis_tac[]) >>
      qexistsl_tac [‘B’, ‘b’, ‘t’] >> rw[endo_lift_def]) >>
    ‘lift_rel (s,r) (t ∘ fbl) (T' f ∘ T' f)’ suffices_by metis_tac[] >>
    subgoal ‘lift_rel (s,r) t (T' f)’ >-
     (drule_then irule t_below_Tf >> rw[] >- (metis_tac[]) >>
      qexistsl_tac [‘B’, ‘b’] >> rw[endo_lift_def]) >>
    irule lift_rel_comp >> rw[] >-
     (metis_tac[endo_def, companion_def, function_def]) >-
     (metis_tac[endo_def, function_def]) >-
     (metis_tac[endo_def, companion_def, function_def]) >-
     (metis_tac[function_def, lub_def]) >-
     (metis_tac[endo_def, companion_def, function_def]) >-
     (‘∀X. s (fbl X) ∧ (∀y. s y ∧ (y = f (b X) ∨ y = b X) ⇒ r y (fbl X)) ∧
           ∀z. s z ∧ (∀y. s y ∧ (y = f (b X) ∨ y = b X) ⇒ r y z) ⇒
               r (fbl X) z’ by fs[lub_def] >>
      rw[lift_rel] >>
      ‘r (t x'') (T' f x'')’ by fs[lift_rel] >>
      first_x_assum $ qspec_then ‘x''’ strip_assume_tac >>
      first_x_assum irule >> pop_assum kall_tac >>
      rw[] >-
       (metis_tac[companion_def, function_def, endo_def]) >-
       (‘lift_rel (s,r) (f ∘ b) (T' f ∘ T' f)’
          suffices_by metis_tac[lift_rel, combinTheory.o_DEF] >>
        irule lift_rel_comp >> rw[SF SFY_ss, endo_function] >-
         (fs[endo_def]) >-
         (metis_tac[companion_def, function_def, endo_def]) >-
         (metis_tac[companion_def, function_def, endo_def]) >-
         (metis_tac[companion_def, function_def, endo_def]) >-
         (irule companion_expansive >>
          qexistsl_tac [‘B’, ‘endo (s,r)’] >> rw[] >>
          metis_tac[endo_poset, endo_lift_def]) >-
         (rw[lift_rel] >>
          drule_then irule poset_trans >>
          rw[SF SFY_ss, endo_in, endo_function] >-
           (metis_tac[companion_def, function_def, endo_def]) >>
          qexists_tac ‘t x'³'’ >> rw[SF SFY_ss, endo_in] >-
           (‘lift_rel (s,r) b t’ suffices_by rw[lift_rel] >>
            drule_then irule compatible_below_companion >>
            metis_tac[compatible_self, function_def, endo_def, lift_rel]) >>
          rfs[lift_rel])) >-
       (drule_then irule poset_trans >> rw[] >-
         (metis_tac[companion_def, function_def, endo_def]) >>
        qexists_tac ‘t x''’ >> rw[] >- (metis_tac[companion_def, function_def]) >>
        metis_tac[compatible_below_companion, compatible_self,
                  function_def, endo_def, lift_rel]))) >-
   (fs[B_join_def, endo_def, endo_lift_def]) >-
   (fs[endo_lift_def]) >-
   (fs[B_join_def, endo_lift_def])
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

Theorem set_companion_compatible:
  monotone b ⇒ set_compatible b (set_companion b)
Proof
  rw[] >>
  subgoal ‘compatible (UNIV,$SUBSET) b (set_companion b)’ >-
   (irule compatible_companion >>
    rw[set_companion, function_def]) >>
  fs[compatible_def, lift_rel, set_compatible_def]
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
  X ⊆ set_companion b {}
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

(* conclude: X is a safe deduction from Y *)
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
Theorem set_param_coind':
  monotone b ∧ (∀X Y. (set_companion b X) ⊆ (set_companion b Y) ∨
                      (set_companion b Y) ⊆ (set_companion b X))
  ⇒ Y ⊆ b (set_companion b (X ∪ Y))
  ⇒ Y ⊆ set_companion b X
Proof
  rw[] >>
  drule_at_then Any irule param_coind' >>
  qexistsl_tac [‘gfp b’, ‘UNIV’] >>
  rw[function_def, set_companion, gfp_poset_gfp, lub_def] >>
  rw[SUBSET_UNION]
QED

Definition set_B_def:
  set_B b = λg X. BIGUNION { f X | f | monotone f ∧ ∀Y. f (b Y) ⊆ b (g Y) }
End

Definition higher_monotone:
  higher_monotone fn = ∀f g. monotone f ∧ monotone g ∧
                             (∀X. f X ⊆ g X) ⇒ (∀X. (fn f) X ⊆ (fn g) X)
End

Definition higher_compat_def:
  higher_compat fn b = ((∀f. monotone f ⇒ monotone (fn f)) ∧ higher_monotone fn ∧
                        ∀f X. monotone f ⇒ (fn (set_B b f)) X ⊆ (set_B b (fn f)) X)
End

Definition set_T_def:
  set_T b = λf X. BIGUNION { (fn f) X | fn | monotone (fn f) ∧ higher_compat fn b }
End

Theorem set_higher_complete:
  complete (endo_lift (𝕌(:α -> bool),$SUBSET))
Proof
  rw[complete_def, endo_lift_def] >-
   (qexists_tac ‘λX. BIGUNION { f X | f | monotone f ∧ c f }’ >>
    rw[lub_def] >-
     (rw[endo_def, monotone_def] >>
      rw[BIGUNION_SUBSET] >>
      rw[BIGUNION, Once SUBSET_DEF] >>
      qexists_tac ‘f X'’ >> rw[] >> metis_tac[SUBSET_DEF]) >-
     (fs[endo_def, lift_rel, BIGUNION, Once SUBSET_DEF] >> metis_tac[]) >>
    fs[lift_rel, endo_def] >> rw[] >>
    irule (iffRL BIGUNION_SUBSET) >> rw[] >> metis_tac[]) >>
  (qexists_tac ‘λX. BIGINTER { f X | f | monotone f ∧ c f }’ >>
   rw[glb_def] >-
    (rw[endo_def, monotone_def] >>
     rw[SUBSET_BIGINTER] >>
     rw[BIGINTER, Once SUBSET_DEF] >>
     metis_tac[SUBSET_DEF]) >-
    (fs[endo_def, lift_rel, BIGINTER, Once SUBSET_DEF] >> metis_tac[]) >>
   fs[lift_rel, endo_def] >> rw[] >>
   irule (iffRL SUBSET_BIGINTER) >> rw[] >> metis_tac[])
QED

(* functionals on sets form a complete lattice under pointwise inclusion
 * B is monotone with that ordering, and it can be defined via lub = BIGUNION
 * hence B has a greatest fixpoint and we can instantiate
 *)
Theorem set_param_coind:
  monotone b
  ⇒ Y ⊆ b (set_companion b (X ∪ Y))
  ⇒ Y ⊆ set_companion b X
Proof
  rw[] >>
  drule_at_then Any irule param_coind >>
  qexistsl_tac [‘set_B b’, ‘set_T b’, ‘gfp b’, ‘UNIV’] >>
  rw[endo_def, set_companion, gfp_poset_gfp, set_higher_complete] >-
   (metis_tac[set_companion_compatible, set_compatible_def]) >-
   (rw[B_join_def, set_B_def, endo_lift_def, endo_def, function_def] >-
     (rw[monotone_def, lift_rel] >>
      rw[BIGUNION_SUBSET] >>
      rw[BIGUNION, Once SUBSET_DEF] >>
      qexists_tac ‘f X''’ >> rw[] >>
      metis_tac[SUBSET_DEF, SUBSET_TRANS]) >-
     (rw[monotonic_def, lift_rel] >>
      rw[BIGUNION_SUBSET] >>
      rw[BIGUNION, Once SUBSET_DEF] >>
      qexists_tac ‘f X'’ >> rw[] >>
      metis_tac[SUBSET_TRANS, monotone_def]) >-
     (rw[lub_def, lift_rel] >-
       (rw[BIGUNION, Once SUBSET_DEF] >> metis_tac[]) >>
      rw[BIGUNION_SUBSET])) >-
   (rw[companion_def, endo_lift_def, set_B_def, set_T_def] >-
     (rw[function_def, endo_def, monotone_def] >>
      rw[BIGUNION_SUBSET] >>
      rw[BIGUNION, Once SUBSET_DEF] >>
      qexists_tac ‘fn f X''’ >> metis_tac[SUBSET_DEF]) >>
    rw[lub_def, endo_def, lift_rel]
    >- (rw[monotone_def, BIGUNION_SUBSET] >>
        rw[BIGUNION, Once SUBSET_DEF] >>
        qexists_tac ‘fn f X''’ >> metis_tac[SUBSET_DEF])
    >- (rw[BIGUNION, Once SUBSET_DEF] >>
        qexists_tac ‘f' f X'’ >> rw[] >>
        qexists_tac ‘f'’ >> rw[] >>
        rw[higher_compat_def, higher_monotone] >-
         (fs[compatible_def, function_def, endo_def, monotonic_def, lift_rel]) >>
        fs[GSYM set_B_def] >>
        fs[compatible_def, lift_rel, endo_def, monotonic_def])
    >- (rw[BIGUNION_SUBSET] >>
        first_x_assum irule >> rw[] >>
        qexists_tac ‘fn’ >> rw[compatible_def] >-
         (rw[function_def, endo_def] >>
          fs[higher_compat_def, higher_monotone]) >-
         (fs[higher_compat_def, higher_monotone] >>
          rw[monotonic_def, lift_rel, endo_def]) >-
         (rw[GSYM set_B_def] >>
          rw[lift_rel] >>
          fs[higher_compat_def, endo_def]))) >>
     (rw[lub_def] >> rw[SUBSET_UNION])
QED

(* Sufficient condition for establishing the linear order on companion values,
   which is hard to state in general since big ordinals aren't supported in HOL4.

   This is essentially a special case of the harder direction of ω-continuity
   - the fact that applying b preserves limits/intersections of ℕ-indexed sets

   similar to the proof in Schafer's thesis, but he uses an L-lattice
 *)
Definition wbounded_def:
  wbounded b = (BIGINTER {FUNPOW b n UNIV | n | T} ⊆ gfp b)
End

Triviality x_in_funpows_gfp:
  wbounded b ⇒
  (∀n. x ⊆ FUNPOW b n UNIV) ⇒ x ⊆ gfp b
Proof
  rw[] >>
  subgoal ‘x ⊆ BIGINTER {FUNPOW b n UNIV | n | T}’ >-
   (fs[BIGINTER, SUBSET_DEF] >> metis_tac[]) >>
  metis_tac[wbounded_def, SUBSET_TRANS]
QED

Triviality FUNPOW_b_mono:
  monotone b ⇒ monotone (FUNPOW b k)
Proof
  strip_tac >>
  Induct_on ‘k’ >- (rw[monotone_def, FUNPOW_0]) >>
  fs[monotone_def, FUNPOW_SUC]
QED

Triviality FUNPOW_UNIV_ord:
  monotone b ⇒
  k' ≤ k ⇒ FUNPOW b k univ(:'a) ⊆ FUNPOW b k' univ(:'a)
Proof
  rw[] >>
  drule LESS_EQUAL_ADD >> rw[] >>
  rw[FUNPOW_ADD] >>
  drule FUNPOW_b_mono >> rw[] >>
  first_x_assum $ qspec_then ‘k'’ strip_assume_tac >>
  fs[monotone_def]
QED

Triviality set_companion_funpow_lemma:
  monotone b ∧
  set_companion b X ⊆ set_companion b (FUNPOW b k UNIV)
  ⇒ set_companion b X ⊆ (FUNPOW b k UNIV)
Proof
  rw[] >>
  drule_then irule SUBSET_TRANS >>
  subgoal ‘FUNPOW b k (set_companion b UNIV) ⊆ FUNPOW b k UNIV’ >-
   (‘monotone (FUNPOW b k)’ by rw[FUNPOW_b_mono] >>
    fs[monotone_def]) >>
  drule_at_then Any irule SUBSET_TRANS >>
  drule set_companion_compatible >>
  rw[set_compatible_def] >>
  subgoal ‘∀m. m ≤ k ⇒
               FUNPOW b (k-m) (set_companion b (FUNPOW b m univ(:'a))) ⊆
                      FUNPOW b k (set_companion b univ(:'a))’ >-
   (Induct_on ‘m’ >- (rw[FUNPOW_0]) >>
    rw[FUNPOW_SUC] >>
    Cases_on ‘k - m’ >-
     (‘¬(SUC m ≤ k)’ suffices_by metis_tac[] >>
      pop_assum mp_tac >> numLib.ARITH_TAC) >>
    ‘m ≤ k’ by metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS] >>
    first_x_assum drule >> rw[] >>
    drule_at_then Any irule SUBSET_TRANS >>
    ‘k - m = SUC n ⇒ k - SUC m = n’ by numLib.ARITH_TAC >>
    rw[FUNPOW] >>
    metis_tac[FUNPOW_b_mono, monotone_def]) >>
  pop_assum $ qspec_then ‘k’ strip_assume_tac >>
  fs[SUB_EQUAL_0]
QED

open whileTheory;
Triviality not_gfp_has_lowest_FUNPOW:
  monotone b ∧ wbounded b ∧
  ¬(X ⊆ gfp b) ⇒
  ∃k. (X ⊆ FUNPOW b k UNIV) ∧ (∀m. X ⊆ FUNPOW b m UNIV ⇒ m ≤ k)
Proof
  rw[] >>
  ‘∃n. ¬(X ⊆ FUNPOW b n UNIV)’ by metis_tac[x_in_funpows_gfp] >>
  subgoal ‘(LEAST n. ¬(X ⊆ FUNPOW b n UNIV)) <> 0’ >-
   (spose_not_then strip_assume_tac >>
    qspec_then ‘λn. ¬(X ⊆ FUNPOW b n UNIV)’ strip_assume_tac
               (cj 1 (iffLR LEAST_EXISTS)) >>
    rfs[] >> gvs[]) >>
  qexists_tac ‘(LEAST n. ¬(X ⊆ FUNPOW b n UNIV)) - 1’ >>
  rw[] >-
   (subgoal ‘∀n. n < (LEAST k. ¬(X ⊆ FUNPOW b k UNIV)) ⇒ ¬¬(X ⊆ FUNPOW b n UNIV)’
    >- (ho_match_mp_tac (cj 2 (iffLR LEAST_EXISTS)) >>
        metis_tac[LEAST_EXISTS]) >>
    fs[]) >>
  spose_not_then strip_assume_tac >>
  fs[NOT_LE] >>
  Cases_on ‘m’ >>
  fs[GSYM LE_LT1] >>
  ‘∀k. (LEAST n. ¬(X ⊆ FUNPOW b n univ(:'a))) ≤ k ⇒ ¬(X ⊆ FUNPOW b k UNIV)’
    suffices_by metis_tac[] >>
  rw[] >>
  qspec_then ‘λn. ¬(X ⊆ FUNPOW b n UNIV)’ strip_assume_tac
             (cj 1 (iffLR LEAST_EXISTS)) >>
  fs[] >>
  metis_tac[FUNPOW_UNIV_ord, SUBSET_TRANS]
QED

Theorem wbounded_companion_final_sequence:
  monotone b ∧ wbounded b ⇒
  if X ⊆ gfp b
  then set_companion b X = gfp b
  else ∃k. set_companion b X = FUNPOW b k UNIV
Proof
  rw[] >-
   (irule lt_gfp_companion >>
    qexistsl_tac [‘b’, ‘ {} ’, ‘$SUBSET’, ‘UNIV’] >>
    rw[bottom_def, set_companion, function_def, gfp_poset_gfp]) >>
  (* there exists a lower bound on b^n⊤ containing X  *)
  ‘∃k. X ⊆ FUNPOW b k UNIV ∧ (∀m. X ⊆ FUNPOW b m UNIV ⇒ m ≤ k)’
    by metis_tac[not_gfp_has_lowest_FUNPOW] >>
  qexists_tac ‘k’ >> rw[] >>
  rw[SET_EQ_SUBSET]
  >- (‘set_companion b X ⊆ set_companion b (FUNPOW b k UNIV)’
        by metis_tac[set_companion_compatible, set_compatible_def, monotone_def] >>
      metis_tac[set_companion_funpow_lemma]) >>
  (* why is this companion compatible? it's all about invalid deductions x ⊊ gfp *)
  irule set_compatible_enhance >> rw[] >>
  qexists_tac ‘λY. if (Y ⊆ gfp b) then {}
                   else BIGINTER { FUNPOW b k UNIV | k | Y ⊆ FUNPOW b k UNIV }’ >>
  rw[] (* we need k to upper bound stuff in the BIGINTER *)
  >- (rw[SUBSET_BIGINTER] >>
      ‘k' ≤ k’ by metis_tac[] >>
      rw[FUNPOW_UNIV_ord]) >>
  rw[set_compatible_def, monotone_def] >-
   (* monotone because X ≤ Y ⇒ X ≤ every b_y, so every b_y is a b_x *)
   (rw[] >- (metis_tac[SUBSET_TRANS]) >>
    rw[SUBSET_BIGINTER] >>
    irule BIGINTER_SUBSET >>
    qexists_tac ‘FUNPOW b k' UNIV’ >> rw[] >>
    metis_tac[SUBSET_TRANS]) >>
  (* compatible because by (and so tby) is bounded above by bb_n = bty *)
  rw[] >- (metis_tac[gfp_greatest_fixedpoint, monotone_def]) >>
  ‘∃k. (Y ⊆ FUNPOW b k UNIV) ∧ (∀m. Y ⊆ FUNPOW b m UNIV ⇒ m ≤ k)’
    by metis_tac[not_gfp_has_lowest_FUNPOW] >>
  ‘b Y ⊆ FUNPOW b (SUC k') UNIV’ by metis_tac[monotone_def, FUNPOW_SUC] >>
  irule BIGINTER_SUBSET >> rw[] >>
  pop_assum $ irule_at Any >>
  rw[FUNPOW_SUC] >>
  fs[monotone_def] >> last_assum irule >>
  rw[SUBSET_BIGINTER] >>
  metis_tac[FUNPOW_UNIV_ord, SUBSET_BIGINTER, monotone_def]
QED

(* alternatively, gfp is the least companion value *)
Triviality gfp_below_funpow:
  monotone b ⇒
  ∀n. gfp b ⊆ FUNPOW b n UNIV
Proof
  strip_tac >>
  Induct >- (rw[FUNPOW_0]) >>
  metis_tac[monotone_def, cj 1 gfp_greatest_fixedpoint, FUNPOW_SUC]
QED

Theorem wbounded_companion_total_order:
  monotone b ∧ wbounded b ⇒
  ∀X Y. set_companion b X ⊆ set_companion b Y ∨
        set_companion b Y ⊆ set_companion b X
Proof
  rw[] >>
  drule_all wbounded_companion_final_sequence >> rw[] >>
  first_assum $ qspec_then ‘X’ strip_assume_tac >>
  first_assum $ qspec_then ‘Y’ strip_assume_tac >>
  Cases_on ‘X ⊆ gfp b’ >> Cases_on ‘Y ⊆ gfp b’ >>
  fs[gfp_below_funpow] >>
  Cases_on ‘k' ≤ k’
  >- (metis_tac[FUNPOW_UNIV_ord])
  >- (‘k ≤ k'’ by fs[LE_CASES] >>
      metis_tac[FUNPOW_UNIV_ord])
QED

Theorem wbounded_param_coind:
  monotone b ∧ wbounded b
  ⇒ Y ⊆ b (set_companion b (X ∪ Y))
  ⇒ Y ⊆ set_companion b X
Proof
  metis_tac[set_param_coind', wbounded_companion_total_order]
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
  rw[monotone_def, llist_functional, pred_setTheory.SUBSET_DEF]
QED

Theorem llist_wbounded:
  wbounded llist_functional
Proof
  rw[wbounded_def, llist_functional] >>
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

(* buffered producer, 3 at a time *)
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

Definition id_enhance_def:
  id_enhance R = R ∪ llist_functional R
End

Theorem id_enhance_mono:
  monotone id_enhance
Proof
  rw[monotone_def, id_enhance_def] >-
   (metis_tac[SUBSET_TRANS, SUBSET_UNION]) >>
  metis_tac[SUBSET_TRANS, SUBSET_UNION, monotone_def, monotone_llist_functional]
QED

Theorem id_enhance_compatible:
  set_compatible llist_functional id_enhance
Proof
  rw[id_enhance_def, set_compatible_def, id_enhance_mono] >-
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
  qexists_tac ‘id_enhance ∘ id_enhance’ >>
  rw[id_enhance_def] >- (rw[llist_functional]) >>
  irule set_compatible_compose >>
  rw[id_enhance_compatible]
QED

Definition cons_rel_def:
  cons_rel R = {x:::xs,y:::ys | x = y ∧ (xs,ys) ∈ R}
End

Theorem cons_rel_cons:
  {(x:::xs,x:::ys)} ⊆ cons_rel R ⇔ {(xs,ys)} ⊆ R
Proof
  rw[cons_rel_def, SUBSET_DEF]
QED

(* incremental accumulation *)
Theorem ones_eq_ones':
  ones = ones'
Proof
  ‘{(ones,ones')} ⊆ UNCURRY $=’ suffices_by rw[SUBSET_DEF] >>
  rewrite_tac[GSYM llist_functional_gfp] >>
  irule set_param_coind_init >> rw[] >>
  irule singleton_subset >> irule set_param_coind >> rw[] >>
  rw[Once ones'_thm, Once ones_thm] >>
  rw[llist_functional] >>
  (* try again *)
  irule singleton_subset >> irule set_param_coind >> rw[] >>
  rw[Once ones_thm] >>
  rw[llist_functional] >>
  (* almost there! ones has taken 2 steps *)
  irule singleton_subset >> irule set_param_coind >> rw[] >>
  rw[Once ones_thm] >>
  rw[llist_functional] >>
  (* the companion is expansive *)
  irule singleton_subset >>
  irule set_param_coind_done >>
  rw[]
QED

Theorem ones_eq_ones'':
  ones = ones'
Proof
  ‘{(ones,ones')} ⊆ UNCURRY $=’ suffices_by rw[SUBSET_DEF] >>
  rewrite_tac[GSYM llist_functional_gfp] >>
  irule set_param_coind_init >> rw[] >>
  irule singleton_subset >>
  irule wbounded_param_coind >> rw[llist_wbounded] >>
  (* unroll thrice  *)
  rw[Once ones'_thm, Once ones_thm, Once ones_thm, Once ones_thm] >>
  rw[llist_functional] >>
  (* work upto cons *)
  irule singleton_subset >>
  irule set_param_coind_upto_f >> rw[] >>
  qexists_tac ‘llist_functional ∘ llist_functional’ >>
  conj_tac >-
   (strip_tac >>
    irule set_compatible_enhance >> rw[] >>
    qexists_tac ‘llist_functional ∘ llist_functional’ >> rw[] >>
    irule set_compatible_compose >>
    rw[set_compatible_self]) >>
  rw[llist_functional] >>
  irule singleton_subset >>
  irule set_param_coind_done >>
  rw[]
QED

(*
  example: inductive companion using duality
 *)

Definition nat_functional_def:
  nat_functional X = λn. n = 0 ∨ ∃k. k ∈ X ∧ n = SUC k
End

Theorem nat_functional_mono:
  monotonic (UNIV,λa b. b ⊆ a) nat_functional
Proof
  rw[monotonic_def, nat_functional_def, SUBSET_DEF]
QED

Theorem nat_functional_lfp:
  gfp (UNIV,λa b. b ⊆ a) nat_functional UNIV
Proof
  rw[gfp_def, nat_functional_def] >-
   (rw[FUN_EQ_THM] >> Cases_on ‘n’ >> rw[]) >>
  rw[FUN_EQ_THM] >>
  qid_spec_tac ‘x’ >> Induct >>
  fs[SUBSET_DEF, IN_DEF]
QED

Theorem super_poset:
  poset (UNIV,λa b. b ⊆ a)
Proof
  rw[poset_def, nat_functional_def, SET_EQ_SUBSET] >>
  metis_tac[SUBSET_TRANS]
QED

Theorem superset_companion:
  companion (UNIV,λa b. b ⊆ a) b
  (λx. BIGINTER { f x | f | compatible (UNIV,λa b. b ⊆ a) b f })
Proof
  rw[companion_def] >- (rw[function_def]) >>
  rw[lub_def, compatible_def, nat_functional_def] >-
   (rw[BIGINTER, Once SUBSET_DEF] >> metis_tac[]) >>
  rw[SUBSET_BIGINTER]
QED

Theorem nat_companion:
  companion (UNIV,λa b. b ⊆ a) nat_functional
  (λx. BIGINTER { f x | f | compatible (UNIV,λa b. b ⊆ a) nat_functional f })
Proof
  metis_tac[superset_companion]
QED

Theorem completeinduct_compatible:
  compatible (UNIV,λa b. b ⊆ a) nat_functional (λP. (λn. ∀k. k ≤ n ⇒ k ∈ P))
Proof
  rw[compatible_def, function_def] >-
   (rw[monotonic_def, SUBSET_DEF] >> metis_tac[]) >>
  rw[lift_rel, SUBSET_DEF, nat_functional_def] >> rw[] >>
  Cases_on ‘k'’ >> rw[]
QED

Theorem COMPLETE_INDUCTION':
  (∀n. (∀m. m < n ⇒ P m) ⇒ P n) ⇒ ∀n. P n
Proof
  ‘(∀n. (∀m. m < n ⇒ P m) ⇒ P n) ⇒ UNIV ⊆ P’
    suffices_by rw[UNIV_DEF, SUBSET_DEF] >>
  strip_tac >>
  ‘(λa b. b ⊆ a) P UNIV’ suffices_by rw[] >>
  assume_tac (INST_TYPE [alpha |-> “:num”] super_poset) >>
  drule_then ho_match_mp_tac companion_coinduct >>
  qexistsl_tac [‘(λx. BIGINTER { f x | f | compatible (UNIV,λa b. b ⊆ a)
                                                      nat_functional f })’,
                ‘nat_functional’] >>
  rw[nat_functional_mono,function_def, superset_companion, nat_functional_lfp] >>
  match_mp_tac SUBSET_TRANS >>
  qexists_tac ‘nat_functional (λn. ∀k. k ≤ n ⇒ k ∈ P)’ >> rw[] >-
   (assume_tac nat_functional_mono >>
    fs[monotonic_def] >> pop_assum irule >>
    assume_tac nat_companion >>
    assume_tac completeinduct_compatible >>
    drule_all compatible_below_companion >>
    fs[lift_rel]) >>
  rw[SUBSET_DEF, IN_DEF] >>
  last_x_assum irule >> rw[] >>
  fs[nat_functional_def]
QED
