(* HOL tutorial ch6 *)

(* reflexive transitive relations *)

val _ = hide "RTC"; (* closure *)
Inductive RTC:
  (∀x.     RTC R x x) ∧
  (∀x y z. R x y ∧ RTC R y z ⇒ RTC R x z)
End

(* what hwppens to free vars in definition?*)
Theorem RTC_RTC:
  ∀R x y z. RTC R x y ⇒ RTC R y z ⇒ RTC R x z
Proof
  strip_tac >>
  Induct_on ‘RTC’ >> rw[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all (cj 2 RTC_rules) >> rw[]
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
  fs[normform_def] >> (* fs loops if passed cases? *)
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
   (fs[diamond_def] >> (* is this normal use of qspec? *)
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
