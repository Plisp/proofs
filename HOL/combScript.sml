(* HOL tutorial ch6 *)

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

(* reflexive transitive relations *)

val _ = hide "RTC"; (* closure *)
Inductive RTC:
  (∀x.     RTC R x x) ∧
  (∀x y z. R x y ∧ RTC R y z ⇒ RTC R x z)
End

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
  ‘∃u. RTC R y u ∧ RTC R z u’ by metis_tac[] >>
  metis_tac[normform_def, RTC_cases]
QED

val _ = hide "diamond";
Definition diamond_def:
  diamond R = ∀x y z. R x l ∧ R x r ⇒ ∃u. R l u ∧ R r u
End

Theorem confluent_diamond_RTC:
  ∀R. confluent R = diamond (RTC R)
Proof
  rw[confluent_def, diamond_def]
QED

Theorem R_RTC_diamond:
  ∀R. diamond R ⇒ ∀x ll r. RTC R x ll ∧ R x r ⇒ ∃u. RTC R ll u ∧ RTC R r u
Proof
  strip_tac >> strip_tac >>
  Induct_on ‘RTC’ >> rw[] >-
   metis_tac[RTC_rules] >-
   (‘∃v. R x' v ∧ R r v’ by metis_tac[diamond_def] >>
    metis_tac[RTC_rules])

QED

Theorem diamond_RTC:
  ∀R. diamond R ⇒ diamond (RTC R)
Proof
  cheat
QED
