{-# OPTIONS --without-K #-}

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤;tt)

variable ℓ ℓ₁ ℓ₂ : Agda.Primitive.Level

data _＝_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  refl : {x : A} → x ＝ x
infix 4 _＝_

ȷ : {A : Set ℓ} (C : (x y : A) → (x ＝ y) → Set ℓ₁)
  → ((x : A) → C x x refl)
  → (x y : A) (p : x ＝ y) → C x y p
ȷ C f x x refl = f x

subst : ∀{ℓ} {A : Set ℓ} {x y : A} (C : A → Set ℓ) → x ＝ y → C x → C y
subst C refl cx = cx

data ⊥ : Set where

data Bad : Nat → Set where
  badt : ⊤ → Bad 0
  badf : ⊥ → Bad 1

{-
  fails to infer type of lambda, using separate f works
-}
f : Bad 1 → ⊥
f (badf ())

negation : (0 ＝ 1) -> ⊥
negation eq = f (subst Bad eq (badt tt))
--negation eq = (\ {badf void -> void} ) (subst Bad eq (badt tt))

{-
  the HoTT definition breaks inference cos of stricter comp rule
-}
_∙_ : {A : Set ℓ} {x y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
_∙_{ℓ} {A} {x}{y}{z} p = ȷ (λ (x y : A) _ → y ＝ z → x ＝ z)
                             (λ x p → p)
                             -- doesn't work
                             --(λ x → (ȷ (λ (x z : A) _ → x ＝ z) (λ x → refl) x z))
                             x y p
infixr 5 _∙_

∙-assoc : {A : Set ℓ} {w x y z : A}
        → (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
        → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙-assoc{ℓ}{A} {w}{x}{y}{z} p q r
  = (ȷ (λ w x (p : w ＝ x) → ∀ (q : x ＝ y) (r : y ＝ z) → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r))
       (λ _ → λ q r → refl{_}{_}{q ∙ r})
         w x p) q r
