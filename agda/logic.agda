{-# OPTIONS --without-K --exact-split --safe #-}

{-
  primitive logical datatypes
-}

open import Agda.Primitive
-- implicitly generalize
variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

{-
  𝟙 (true)
-}

data ⊤ : Set where
  ⋆ : ⊤
𝟙 = ⊤

ind⊤ : (A : ⊤ → Set ℓ) → A ⋆ → ((x : ⊤) → A x)
ind⊤ A a ⋆ = a

-- rec = ind w/ constant target family
rec⊤ : (A : Set ℓ) → A → (⊤ → A) -- a = base case
rec⊤ A a ⋆ = ind⊤ (λ _ → A) a ⋆

{-
  𝟘 (false)
-}

data ⊥ : Set where
𝟘 = ⊥

ind⊥ : (A : ⊥ → Set ℓ) → ((x : ⊥) → A x)
ind⊥ A ()

-- convenient
rec⊥ : (A : Set ℓ) → (⊥ → A)
rec⊥ A ()

¬_ : Set ℓ → Set ℓ
¬ X = X → ⊥
infix 3 ¬_

{-
  product (AND)
-}

data _×_ (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  _,_ : A → B → A × B
infixr 2 _×_
infixr 4 _,_

ind× : {A : Set ℓ₁} {B : Set ℓ₂}
     → (C : A × B → Set ℓ)
     → ((x : A) → (y : B) → C (x , y))
     → ((z : A × B) → C z)
ind× C f (a , b) = f a b

-- pattern matching projections, generally more convenient
fst : {A : Set ℓ₁} {B : Set ℓ₂} → A × B → A
fst (x , y) = x

snd : {A : Set ℓ₁} {B : Set ℓ₂} → A × B → B
snd (x , y) = y

{-
  coproduct (OR)
-}

data _＋_ (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  inl : A → A ＋ B
  inr : B → A ＋ B
infixr 1 _＋_

ind＋ : {A : Set ℓ₁} {B : Set ℓ₂}
      → (C : A ＋ B → Set ℓ)
      → ((x : A) → C (inl x)) → ((y : B) → C (inr y))
      → ((z : A ＋ B) → C z)
ind＋ C ax ay (inl x) = ax x
ind＋ C ax ay (inr y) = ay y

rec＋ : {A : Set ℓ₁} {B : Set ℓ₂}
     → (C : Set ℓ)
     → (A → C) → (B → C)
     → (A ＋ B) → C
rec＋ C = ind＋ (λ _ → C)

{-
  dependent sum (there exists)
-}

-- data Σ {A : Set ℓ} (B : A → Set ℓ₁) : Set (ℓ ⊔ ℓ₁) where
--   _,_ : (a : A) → B a → Σ B

-- gives eta (uniqueness) rules
record Σ {X : Set ℓ} (Y : X → Set ℓ₁) : Set (ℓ ⊔ ℓ₁) where
  constructor
   _,_
  field
   p1 : X
   p2 : Y p1

indΣ : {A : Set ℓ} {B : A → Set ℓ₁}
      → (C : Σ B → Set ℓ₂)
      → ((x : A) (y : B x) → C (x , y))
      → ((z : Σ B) → C z)
indΣ C f (x , y) = f x y

pr₁ : {A : Set ℓ} {B : A → Set ℓ₁} → Σ B → A
pr₁ (x , y) = x

pr₂ : {A : Set ℓ} {B : A → Set ℓ₁} → (z : Σ B) → B (pr₁ z)
pr₂ (x , y) = y

-Σ : (A : Set ℓ) (B : A → Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
-Σ A B = Σ B
syntax -Σ A (λ a → b) = Σ a ∶ A , b -- \:1
infix 0 -Σ

{-
  dependent product (forall, implies)
-}

Π : {X : Set ℓ} (A : X → Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
Π {X = X} A = (x : X) → A x

-Π : (X : Set ℓ) (Y : X → Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
-Π X Y = Π Y
syntax -Π A (λ x → b) = Π x ∶ A , b
infix 0 -Π

id : {T : Set ℓ} → T → T
id a = a

_∘_ : {A : Set ℓ} {B : Set ℓ₁} {C : B → Set ℓ₂}
    → ((b : B) → C b) → (f : A → B) → ((x : A) → C (f x))
g ∘ h = λ x → g (h x)
infixr 6 _∘_

{-
  propositional equality
-}
data _＝_ {A : Set ℓ} : A → A → Set ℓ where
  refl : (x : A) → x ＝ x
infix 4 _＝_
{-# BUILTIN EQUALITY _＝_ #-}

-- induction
ȷ : {A : Set ℓ} (C : (x y : A) → (x ＝ y) → Set ℓ₁)
  → ((x : A) → C x x (refl x))
  → (x y : A) (p : x ＝ y) → C x y p
ȷ C f x x (refl x) = f x

-- based path induction
ⅉ : {A : Set ℓ} (a : A) → (C : (x : A) → (a ＝ x) → Set ℓ₁)
  → C a (refl a)
  → (x : A) (p : a ＝ x) → C x p
ⅉ a C ca x (refl x) = ca
