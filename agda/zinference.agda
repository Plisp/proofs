{-# OPTIONS --without-K #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Nat using (Nat;zero;suc;_+_)
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
    lemma g y = ap g (pr₂ (s y))

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
       (λ _ → λ q r → refl{x = q ∙ r})
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

{-
  fib termination
-}

ap2 : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ} {w x : A} {y z : B}
    → (f : A → B → C) → (w ≡ x) → (y ≡ z) → (f w y ≡ f x z)
ap2{ℓ₁}{ℓ₂}{ℓ} {A}{B}{C} {w}{x}{y}{z} f p q
  = trans (cong (λ x → f x y) p) (cong (λ y → f x y) q)


fib : Nat → Nat
fib 0 = 0
fib 1 = 1
fib (suc (suc a)) = fib a + fib (suc a)

data ℕ₂ : Set where
  0₂ : ℕ₂
  1₂ : ℕ₂

data ℕ₃ : Set where
  0₃ : ℕ₃
  1₃ : ℕ₃
  2₃ : ℕ₃

suc₂ : ℕ₂ → ℕ₂
suc₂ 0₂ = 1₂
suc₂ 1₂ = 0₂

mod2 : Nat → ℕ₂
mod2 zero = 0₂
mod2 (suc x) = suc₂ (mod2 x)

_+₂_ : ℕ₂ → ℕ₂ → ℕ₂
0₂ +₂ y = y
1₂ +₂ 0₂ = 1₂
1₂ +₂ 1₂ = 0₂

+₂-rule : ∀ {n m : ℕ₂} → (suc₂ n) +₂ m ≡ suc₂ (n +₂ m)
+₂-rule {0₂} {0₂} = refl
+₂-rule {0₂} {1₂} = refl
+₂-rule {1₂} {0₂} = refl
+₂-rule {1₂} {1₂} = refl

plus-mod2 : (n m : Nat) → mod2 n +₂ mod2 m ≡ mod2 (n + m)
plus-mod2 zero m = refl
plus-mod2 (suc n) m =
  begin mod2 (suc n) +₂ mod2 m
    ≡⟨⟩ suc₂ (mod2 n) +₂ mod2 m
    ≡⟨ +₂-rule {mod2 n} {mod2 m} ⟩ suc₂ (mod2 n +₂ mod2 m)
    ≡⟨ cong suc₂ (plus-mod2 n m) ⟩ suc₂ (mod2 (n + m))
    ≡⟨⟩ mod2 (suc (n + m))
    ≡⟨⟩ mod2 ((suc n) + m)
  ∎

suc₃ : ℕ₃ → ℕ₃
suc₃ 0₃ = 1₃
suc₃ 1₃ = 2₃
suc₃ 2₃ = 0₃

mod3 : Nat → ℕ₃
mod3 zero = 0₃
mod3 (suc x) = suc₃ (mod3 x)

-- can do without mutual: generalize the IH using data
mutual
  plus-mod2-lem : (n : Nat) → mod2 (fib n + fib (suc n))
                          ≡ mod2 (fib n) +₂ mod2 (fib (suc n))
  plus-mod2-lem n = sym (plus-mod2 (fib n) (fib (suc n)))

  tripl-fib-even2 : (n : Nat) → mod3 n ≡ 0₃ → mod2 (fib n) ≡ 0₂
  tripl-fib-even2 0 _ = refl
  tripl-fib-even2 1 ()
  tripl-fib-even2 (suc (suc n)) with mod3 n | ind1 n
  ...                                | 0₃   | _   = λ ()
  ...                                | 1₃   | lem = λ _ → lem refl
  ...                                | 2₃   | _   = λ ()

  ind1 : ∀ n → mod3 n ≡ 1₃ → mod2 (fib (suc (suc n))) ≡ 0₂
  ind1 n p = begin       mod2 (fib n  +  fib (suc n))
    ≡⟨ plus-mod2-lem n ⟩ mod2 (fib n) +₂ mod2 (fib (suc n))
    ≡⟨ ap2 (λ a b → a +₂ b) (trip1-fib-odd2 n p)
                            (trip2-fib-odd2 (suc n) (cong suc₃ p)) ⟩
    1₂ +₂ 1₂ ≡⟨⟩ 0₂ ∎

  trip1-fib-odd2 : (n : Nat) → mod3 n ≡ 1₃ → mod2 (fib n) ≡ 1₂
  trip1-fib-odd2 0 ()
  trip1-fib-odd2 1 _ = refl
  trip1-fib-odd2 (suc (suc n)) with mod3 n  | ind2 n
  ...                                | 0₃   | _   = λ ()
  ...                                | 1₃   | _   = λ ()
  ...                                | 2₃   | lem = λ _ → lem refl

  ind2 : ∀ n → mod3 n ≡ 2₃ → mod2 (fib (suc (suc n))) ≡ 1₂
  ind2 n p = trans (plus-mod2-lem n)
                   (ap2 (λ a b → a +₂ b) (trip2-fib-odd2 n p)
                                         (tripl-fib-even2 (suc n) (cong suc₃ p)))

  trip2-fib-odd2 : (n : Nat) → mod3 n ≡ 2₃ → mod2 (fib n) ≡ 1₂
  trip2-fib-odd2 0 ()
  trip2-fib-odd2 1 ()
  trip2-fib-odd2 (suc (suc n)) with mod3 n
  ...                          | 0₃ = {!!}
  ...                          | 1₃ = λ ()
  ...                          | 2₃ = λ ()
