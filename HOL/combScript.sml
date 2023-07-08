(* HOL tutorial ch6 *)

(* reflexive transitive relations *)

val _ = hide "RTC"; (* closure *)
Inductive RTC:
  (∀x.     RTC R x x) ∧
  (∀x y z. R x y ∧ RTC R y z ⇒ RTC R x z)
End

Theorem RTC_RTC:
  ∀R x y z. RTC R x y ⇒ RTC R y z ⇒ RTC R x z
Proof
  strip_tac >>
  Induct_on ‘RTC’ >> rw[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all (cj 2 RTC_rules) >> rw[]
QED

Theorem RTC_monotone:
  ∀R S. (∀x y. R x y ⇒ S x y) ⇒ (∀x y. RTC R x y ⇒ RTC S x y)
Proof
  strip_tac >> strip_tac >>
  Induct_on ‘RTC’ >> rw[] >-
   fs[RTC_rules] >-
   (fs[] >>
    pop_assum drule >> strip_tac >>
    drule_all (cj 2 RTC_rules) >> rw[])
QED

Definition confluent_def:
  confluent R = ∀ x y z. RTC R x y ∧ RTC R x z ⇒ ∃u. RTC R y u ∧ RTC R z u
End

Definition normform_def:
  normform R x = ∀y. ~(R x y)
End

Theorem confluent_normforms_unique:
  ∀R. confluent R ⇒ ∀x y z. RTC R x y ∧ normform R y ∧
                            RTC R x z ∧ normform R z ⇒ y = z
Proof
  rw[confluent_def] >>
  pop_last_assum (qspecl_then [‘x’,‘y’,‘z’] strip_assume_tac) >>
  pop_assum drule_all >> strip_tac >>
  fs[normform_def] >> (* fs loops if passed cases *)
  metis_tac[RTC_cases] (* proof is case analysis on RTC *)
QED

val _ = hide "diamond";
Definition diamond_def:
  diamond R = ∀x l r. R x l ∧ R x r ⇒ ∃u. R l u ∧ R r u
End

Theorem confluent_diamond_RTC:
  ∀R. confluent R = diamond (RTC R)
Proof
  rw[confluent_def, diamond_def]
QED

Theorem R_RTC_diamond:
  ∀R. diamond R ⇒ ∀x rr l. RTC R x rr ∧ R x l ⇒ ∃u. RTC R rr u ∧ RTC R l u
Proof
  strip_tac >> strip_tac >>
  Induct_on ‘RTC’ >> rw[] >-
   (qexists_tac `l` >> CONJ_TAC >-
     (‘RTC R l l’ by rw[RTC_rules] >> drule_all (cj 2 RTC_rules) >> rw[]) >-
     rw[RTC_rules]) >-
   (fs[diamond_def] >>
    pop_last_assum (qspecl_then [‘x’,‘l’,‘x'’] strip_assume_tac) >>
    pop_assum drule_all >> strip_tac >>
    last_x_assum (qspec_then ‘u’ strip_assume_tac) >>
    pop_assum drule >> strip_tac >>
    qspecl_then [‘R’,‘l’,‘u’,‘u'’] strip_assume_tac (cj 2 RTC_rules) >>
    pop_assum drule >> strip_tac >>
    qexists_tac ‘u'’ >> rw[])
QED

Theorem diamond_RTC:
  ∀R. diamond R ⇒ diamond (RTC R)
Proof
  rpt strip_tac >> simp[diamond_def] >>
  Induct_on ‘RTC R x y’ >> rw[] >-
   (‘RTC R r r’ by rw[RTC_rules] >>
    qexists_tac ‘r’ >> rw[]) >-
   (drule_all R_RTC_diamond >> strip_tac >>
    last_x_assum (qspec_then ‘u’ strip_assume_tac) >>
    pop_assum drule >> strip_tac >>
    qspecl_then [‘R’,‘r’,‘u’,‘u'’] strip_assume_tac RTC_RTC >>
    pop_assum drule_all >> strip_tac >>
    qexists_tac ‘u'’ >> rw[])
QED

(* back to combinators *)

val _ = hide "K";
val _ = hide "S";
Datatype:
  cl = K | S | # cl cl
End

val _ = set_fixity "#" (Infixl 1100);

val _ = set_mapped_fixity {fixity = Infix(NONASSOC, 450), tok = "-->", term_name = "redn"};
Inductive redn:
  (∀x y f. x --> y ⇒ f # x --> f # y) ∧
  (∀f g x. f --> g ⇒ f # x --> g # x) ∧
  (∀x y.   K # x # y --> x) ∧
  (∀f g x. S # f # g # x --> (f # x) # (g # x))
End

val _ = set_fixity "-->*" (Infix(NONASSOC, 450));
Overload "-->*" = “RTC redn”;

val _ = set_mapped_fixity {fixity = Infix(NONASSOC, 450), tok = "-|>", term_name = "predn"};
Inductive predn:
  (∀x. x -|> x) ∧
  (∀x y u v. x -|> y ∧ u -|> v ⇒ x # u -|> y # v) ∧
  (∀x y. K # x # y -|> x) ∧
  (∀f g x. S # f # g # x -|> (f # x) # (g # x))
End

val _ = set_fixity "-|>*" (Infix(NONASSOC, 450));
Overload "-|>*" = “RTC predn”;

Theorem RTCredn_RTCpredn:
  ∀x y. x -->* y ⇒ x -|>* y
Proof
  match_mp_tac RTC_monotone >>
  Induct_on ‘x --> y’ >>
  metis_tac[predn_rules] (* big case analysis *)
QED

Theorem RTC_redn_ap_congruence:
  ∀x y. x -->* y ⇒ ∀z. (x # z -->* y # z) ∧ (z # x -->* z # y)
Proof
  Induct_on ‘x -->* y’ >> rw[RTC_rules] >>
  pop_assum (qspec_then ‘z’ strip_assume_tac) >>
  metis_tac[redn_rules, RTC_rules] (* obvious by definition *)
QED

Theorem predn_RTCredn:
  ∀x y. x -|> y ⇒ x -->* y
Proof
  Induct_on ‘x -|> y’ >> rw[RTC_rules] >-
   (drule (cj 2 RTC_redn_ap_congruence) >> strip_tac >>
    pop_assum (qspec_then ‘x’ strip_assume_tac) >>
    rev_drule (cj 1 RTC_redn_ap_congruence) >> strip_tac >>
    pop_assum (qspec_then ‘y'’ strip_assume_tac) >>
    drule_all RTC_RTC >> rw[]) >-
   metis_tac[RTC_cases, redn_rules] >-
   metis_tac[RTC_cases, redn_rules]
QED

Theorem RTCpredn_RTCredn:
  ∀x y. x -|>* y ⇒ x -->* y
Proof
  Induct_on ‘RTC’ >> rw[RTC_rules] >>
  drule predn_RTCredn >> strip_tac >>
  drule_all RTC_RTC >> rw[]
QED

Theorem RTCpredn_EQ_RTCredn:
  $-|>* = $-->*
Proof
  rw[FUN_EQ_THM, EQ_IMP_THM, RTCpredn_RTCredn, RTCredn_RTCpredn]
QED

(* diamond property *)

fun characterise t = SIMP_RULE (srw_ss()) [] (SPEC t predn_cases);

val K_predn = characterise “K”;
val S_predn = characterise “S”;
val Sx_predn0 = characterise “S # x”;

Theorem Sx_predn[local]:
  ∀x y. S # x -|> y
⇔ ∃z. y = S # z ∧ x -|> z
Proof
  rw[Sx_predn0, predn_rules, S_predn, EQ_IMP_THM]
QED

Theorem Kx_predn[local]:
  ∀x y. K # x -|> y ⇔ ∃z. y = K # z ∧ x -|> z
Proof
  rw[characterise “K # x”, predn_rules, K_predn, EQ_IMP_THM]
QED

Theorem Kxy_predn[local]:
  ∀x y z. K # x # y -|> z
⇔ (∃u v. z = K # u # v ∧ x -|> u ∧ y -|> v)
  ∨ z = x
Proof
  rw[characterise “K # x # y”, predn_rules, Kx_predn, EQ_IMP_THM]
QED

Theorem Sxy_predn[local]:
  ∀x y z. S # x # y -|> z
⇔ ∃u v. z = S # u # v ∧ x -|> u ∧ y -|> v
Proof
  rw[characterise “S # x # y”, predn_rules, Sx_predn, EQ_IMP_THM]
QED

Theorem Sxyz_predn[local]:
  ∀w x y z. S # w # x # y -|> z
⇔ (∃p q r. z = S # p # q # r ∧ w -|> p ∧ x -|> q ∧ y -|> r)
  ∨ z = (w # y) # (x # y)
Proof
  rw[characterise “S # w # x # y”, predn_rules, Sxy_predn, EQ_IMP_THM]
QED

val x_ap_y_predn = characterise “x # y”;

Theorem predn_diamond_lemma[local]:
  ∀x y. x -|> y ⇒ ∀z. x -|> z ⇒ ∃u. y -|> u ∧ z -|> u
Proof
  Induct_on ‘x -|> y’ >> rpt conj_tac >-
   metis_tac[predn_rules] >-
   (rw[] >>
    first_assum (strip_assume_tac o SIMP_RULE(srw_ss())[x_ap_y_predn]) >> rw[] >-
     metis_tac[predn_rules] >-
     metis_tac[predn_rules] >-
     (qspecl_then [‘z’,‘y’] strip_assume_tac (iffLR Kx_predn) >> rw[] >>
      pop_assum drule_all >> strip_tac >>
      metis_tac[predn_rules]) >-
     (qspecl_then [‘f’,‘g’,‘y’] strip_assume_tac (iffLR Sxy_predn) >> rw[] >>
      pop_assum drule_all >> strip_tac >>
      metis_tac[predn_rules])) >-
   (rw[Kxy_predn] >> metis_tac[predn_rules]) >-
   (rw[Sxyz_predn] >> metis_tac[predn_rules])
QED

Theorem predn_diamond[local]:
  diamond predn
Proof
  rw[diamond_def] >>
  irule predn_diamond_lemma >>
  qexists_tac ‘x’ >> rw[]
QED

Theorem confluent_redn:
  confluent redn
Proof (* how to rewrite using an equality? *)
  rw[confluent_diamond_RTC, GSYM RTCpredn_EQ_RTCredn, (* flip equality *)
     MATCH_MP diamond_RTC predn_diamond] (* modus ponens *)
QED
