{-# OPTIONS --without-K #-}

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤;tt)
open import Agda.Primitive

variable ℓ ℓ₁ ℓ₂ : Level

_∘_ : {A : Set ℓ} {B : Set ℓ₁} {C : B → Set ℓ₂}
    → ((b : B) → C b) → (f : A → B) → ((x : A) → C (f x))
g ∘ h = λ x → g (h x)
infixr 6 _∘_

data _＝_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  refl : {x : A} → x ＝ x
infix 4 _＝_

ȷ : {A : Set ℓ} (C : (x y : A) → (x ＝ y) → Set ℓ₁)
  → ((x : A) → C x x refl)
  → (x y : A) (p : x ＝ y) → C x y p
ȷ C f x x refl = f x

-- symmetry
flip : {A : Set ℓ} {x y : A} → (x ＝ y) → (y ＝ x)
flip {ℓ} {A} {x}{y} p = ȷ (λ x y _ → y ＝ x) (λ x → refl) x y p

-- transitivity
_∙_ : {A : Set ℓ} {x y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
_∙_{ℓ} {A} {x}{y}{z} p = ȷ (λ (x y : A) _ → y ＝ z → x ＝ z)
                             (λ x p → p)
                             -- doesn't work
                             --(λ x → (ȷ (λ (x z : A) _ → x ＝ z) (λ x → refl) x z))
                             x y p
infixr 5 _∙_

ap : {A : Set ℓ} {B : Set ℓ₁} {x y : A}
   → (f : A → B) → (x ＝ y) → (f x ＝ f y)
ap {ℓ}{ℓ₁} {A}{B} {x}{y} f p = ȷ (λ x y _ → f x ＝ f y)
                                 (λ x → refl)
                                 x y p

record Σ {X : Set ℓ} (Y : X → Set ℓ₁) : Set (ℓ ⊔ ℓ₁) where
  constructor
   _,_
  field
   x : X
   y : Y x

pr₁ : {A : Set ℓ} {B : A → Set ℓ₁} → Σ B → A
pr₁ (x , y) = x

pr₂ : {A : Set ℓ} {B : A → Set ℓ₁} → (z : Σ B) → B (pr₁ z)
pr₂ (x , y) = y

-Σ : (A : Set ℓ) (B : A → Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
-Σ A B = Σ B
syntax -Σ A (λ a → b) = Σ a ∶ A , b -- \:1
infix 0 -Σ

data ⊥ : Set where

{-
  epicness
-}

surj : {A B : Set} (f : A → B) → Set
surj {A}{B} f = (∀ (y : B) → Σ x ∶ A , f x ＝ y)

-- homotopy equality instead of funext
epic : {A B : Set} (C : Set) (f : A → B) → Set
epic {A}{B} C f = ∀ (g h : B → C) → (∀ x → (g ∘ f)x ＝ (h ∘ f)x) → (∀ y → g y ＝ h y)

surj→epic : {A B C : Set} (f : A → B)
          → surj f → epic C f
surj→epic {A}{B}{C} f s g h p y = flip (lemma g y) ∙ p (pr₁ (s y)) ∙ (lemma h y)
  where
    lemma : (g : B → C) → ∀ y → g (f (pr₁ (s y))) ＝ g y
    lemma g y = ap (λ x → g x) (pr₂ (s y))

-- requires HIT https://1lab.dev/Data.Set.Surjection.html#epis-are-surjective
-- not easy to reverse f without LEM

-- epic→surj : {A B C : Set} (f : A → B)
--           → epic C f → surj f
-- epic→surj {A}{B}{C} f p = {!!}

{-
  the HoTT definition breaks inference cos of stricter comp rule
-}

∙-assoc : {A : Set} {w x y z : A}
        → (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
        → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙-assoc {A} {w}{x}{y}{z} p q r
  = (ȷ (λ w x (p : w ＝ x) → ∀ (q : x ＝ y) (r : y ＝ z) → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r))
       (λ _ → λ q r → refl{_}{_}{q ∙ r})
         w x p) q r

{-
  fails to infer type of lambda, using separate f works
-}

data Bad : Nat → Set where
  badt : ⊤ → Bad 0
  badf : ⊥ → Bad 1

subst : {A : Set} {x y : A} (C : A → Set) → x ＝ y → C x → C y
subst C refl cx = cx

f : Bad 1 → ⊥
f (badf ())

negation : (0 ＝ 1) -> ⊥
negation eq = f (subst Bad eq (badt tt))
--negation eq = (\ {badf void -> void} ) (subst Bad eq (badt tt))
