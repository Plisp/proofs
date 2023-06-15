(* ∃ reason for both tuples and pairs *)
(* ∃ diff between single, double quotes *)
(* ∃ a way to collect a proof *)
(* ∃ a way to rewrite using a hypothesis *)

(* ocaml, parsed *)
(* fun zip(l1,l2) = *)
(*   if null l1 orelse null l2 then [] *)
(*   else (hd l2, hd l2) :: zip(tl l1, tl l2); *)

(* open HolKernel boolLib Parse bossLib; *)
open arithmeticTheory;

(*val _ = new_theory "euclid"; *)

Definition divides_def:
  divides a b = ∃x. a * x = b
End

val _ = set_fixity "divides" (Infix(NONASSOC, 450));

(* x = 0 ∨ x' = 0 case analysis on x *)
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
  ‘∀p m. 0 < m ⇒ m divides (FACT (m+p))’ suffices_by metis_tac[LESS_EQ_EXISTS] >>
  Induct_on ‘p’ >| [
    Cases_on ‘m’ >| [
      fs[], (* simplifies assumptions *)
      rw[FACT, DIVIDES_LMUL, DIVIDES_REFL]
    ],
    rw[FACT, ADD_CLAUSES, DIVIDES_RMUL]
  ]
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
  metis_tac[DIVIDES_LE, DIVIDES_ZERO, DECIDE “2 ≠ 0”,
            DECIDE “x ≤ 2 ⇔ (x=0) ∨ (x=1) ∨ (x=2)”]
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
  Cases_on ‘prime n’ >| [
    metis_tac[DIVIDES_REFL],
    ‘∃x. x divides n ∧ x≠1 ∧ x≠n’ by metis_tac[prime_def] >>
    ‘x<n ∨ n=0’ by metis_tac[DIVIDES_LE, LESS_OR_EQ] >| [
      metis_tac[DIVIDES_TRANS], (* need ind to get factor of x | n *)
      qexists_tac ‘2’ (* any prime divides 0 *) >> rw[PRIME_2, DIVIDES_0]
    ]
  ]
QED

Theorem EUCLID:
  ∀n. ∃p. n < p ∧ prime p
Proof
  spose_not_then strip_assume_tac >>
  mp_tac (SPEC “FACT n + 1” PRIME_FACTOR) >> (* replaces ∀x.x -> ∀n. fact n + 1 *)
  rw[FACT_LESS, DECIDE “x≠0 ⇔ 0<x”] >> (* DECIDE converts term to theorem *)
  rw[GSYM IMP_DISJ_THM] >> (* ~A ∨ B |- A ⇒ B *)
  metis_tac[DIVIDES_FACT, DIVIDES_ADDL, DIVIDES_ONE,
            NOT_PRIME_1, NOT_LESS, PRIME_POS]

QED

(* val _ = export_theory(); *)
