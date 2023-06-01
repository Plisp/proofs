open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤;tt)

data _＝_ {n} {A : Set n} : A → A → Set n where
  refl : {x : A} → x ＝ x

ȷ : {A : Set} {x y : A} (C : A → Set) → x ＝ y → C x → C y
ȷ C refl cx = cx

data ⊥ : Set where

data Bad : Nat → Set where
  badt : ⊤ → Bad 0
  badf : ⊥ → Bad 1

f : Bad 1 → ⊥
f (badf ())

-- fails to infer type, using f works
negation : (0 ＝ 1) -> ⊥
negation eq = f (ȷ Bad eq (badt tt))
--negation eq = (\ {badf void -> void} ) (ȷ Bad eq (badt tt))
