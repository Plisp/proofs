(* sml embed *)
(* fun zip(l1,l2) = *)
(*   if null l1 orelse null l2 then [] *)
(*   else (hd l2, hd l2) :: zip(tl l1, tl l2); *)

(* drule_then strip_assume_tac THEOREM *)
(* mp_tac push theorem as implication before goal *)
(* conj_tac split on conjunction goal *)
(* mp elim irule_at (Pos hd) Pos : hd/last/list.nth/Any (conjunct list ) -> position *)

(* open HolKernel boolLib Parse bossLib; *)
open arithmeticTheory;

(*val _ = new_theory "euclid"; *)

Definition divides_def:
  divides a b = ∃x. a * x = b
End

val _ = set_fixity "divides" (Infix(NONASSOC, 450));

Theorem DIVIDES_0:
  ∀x. x divides 0
Proof
  rw[divides_def] >> qexists_tac ‘0’ >> rw[]
QED

Theorem DIVIDES_ZERO:
  ∀x. 0 divides x ⇔ (x = 0)
Proof
  rw[divides_def]
QED

Theorem DIVIDES_ONE:
  ∀x. x divides 1 ⇔ (x = 1)
Proof
  rw[divides_def]
QED

Theorem DIVIDES_REFL:
  ∀x. x divides x
Proof
  rw[divides_def] >> qexists_tac ‘1’ >> rw[]
QED

Theorem DIVIDES_TRANS:
  ∀a b c. a divides b ∧ b divides c ⇒ a divides c
Proof
  rw[divides_def] >> qexists_tac ‘x * x'’ >> rw[]
QED

Theorem DIVIDES_ADD:
  ∀d a b. d divides a ∧ d divides b ⇒ d divides (a+b)
Proof
  rw[divides_def] >> qexists_tac ‘x + x'’ >> rw[]
QED

Theorem DIVIDES_SUB:
  ∀d a b. d divides a ∧ d divides b ⇒ d divides (a - b)
Proof
  rw[divides_def] >> qexists_tac ‘x - x'’ >> rw[]
QED

Theorem DIVIDES_ADDL:
  ∀d a b. d divides a ∧ d divides (a+b) ⇒ d divides b
Proof
  rw[divides_def] >> qexists_tac ‘x' - x’ >> rw[]
QED

Theorem DIVIDES_LMUL:
  ∀d a x. d divides a ⇒ d divides (x * a)
Proof
  rw[divides_def] >> qexists_tac ‘x' * x’ >> rw[]
QED

Theorem DIVIDES_RMUL:
  ∀d a x. d divides a ⇒ d divides (a * x)
Proof
  rw[divides_def] >> qexists_tac ‘x * x'’ >> rw[]
QED

Theorem DIVIDES_LE:
  ∀m n. m divides n ⇒ m ≤ n ∨ n = 0
Proof
  rw[divides_def] >> rw[]
QED

Theorem DIVIDES_FACT:
  ∀m n. 0 < m ∧ m ≤ n ⇒ m divides (FACT n)
Proof
  rpt strip_tac >>
  gvs[LESS_EQ_EXISTS] >>
  Induct_on ‘p’ >- (* combinator solves first case using tactic *)
   (Cases_on ‘m’ >> fs[FACT, DIVIDES_LMUL, DIVIDES_REFL]) >- (* applied to both *)
   rw[FACT, ADD_CLAUSES, DIVIDES_RMUL]
QED

(* primality *)
Definition prime_def:
  prime p ⇔ p ≠ 1 ∧ ∀x. x divides p ⇒ (x = 1) ∨ (x = p)
End

Theorem NOT_PRIME_0:
  ~prime 0
Proof
  rw[prime_def, DIVIDES_0]
QED

Theorem NOT_PRIME_1:
  ~prime 1
Proof
  rw[prime_def]
QED

Theorem PRIME_2:
  prime 2
Proof
  rw[prime_def] >>
  drule DIVIDES_LE >>
  rw[LESS_OR_EQ] >>
  gvs[DIVIDES_ZERO, DECIDE “x < 2 ⇔ (x=0) ∨ (x=1)”]
QED

Theorem PRIME_POS:
  ∀p. prime p ⇒ 0<p
Proof
  Cases >>
  rw[NOT_PRIME_0]
QED

(* 4.3 primality *)
Theorem PRIME_FACTOR:
  ∀n. n≠1 ⇒ ∃p. prime p ∧ p divides n
Proof
  completeInduct_on ‘n’ >> (* strong induction *)
  rw[] >>
  Cases_on ‘prime n’ >-
   (qexists_tac ‘n’ >> rw[DIVIDES_REFL]) >-
   (‘∃x. x divides n ∧ x≠1 ∧ x≠n’ by (* by also splits <- into multiple assums *)
      (gvs[prime_def] >> first_assum $ irule_at $ Pos hd >> simp[]) >>
    Cases_on ‘n’ >-
     (qexists_tac ‘2’ >> rw[PRIME_2, DIVIDES_0, prime_def]) >-
     (drule_then strip_assume_tac DIVIDES_LE >>
      rfs[LESS_OR_EQ] >>
      last_assum (drule_all_then strip_assume_tac) >>
      qexists_tac ‘p’ >>
      rw[] >>
      irule DIVIDES_TRANS >>
      qexists_tac ‘x’ >>
      rw[]))
QED

(* infinity of primes *)
Theorem EUCLID:
  ∀n. ∃p. n < p ∧ prime p
Proof
  spose_not_then strip_assume_tac >> (* proof by contradiction *)
  qspec_then ‘FACT n + 1’ mp_tac PRIME_FACTOR >> (* instantiates ∀x.x *)
  rw[FACT_LESS, DECIDE “x≠0 ⇔ 0<x”] >> (* DECIDE converts term to theorem *)
  rw[GSYM IMP_DISJ_THM] >> (* ~A ∨ B |- A ⇒ B *)
  last_x_assum $ drule o ONCE_REWRITE_RULE[DECIDE “(A ⇒ ¬B) ⇔ (B ⇒ ¬A)”] >>
  rw[NOT_LESS] >>
  drule_then strip_assume_tac PRIME_POS >>
  drule_all_then strip_assume_tac DIVIDES_FACT >>
  spose_not_then strip_assume_tac >>
  drule_all_then strip_assume_tac DIVIDES_ADDL >>
  fs[DIVIDES_ONE, NOT_PRIME_1]
QED

(* val _ = export_theory(); *)
