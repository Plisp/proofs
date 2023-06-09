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

⊤-ind : (A : ⊤ → Set ℓ) → A ⋆ → ((x : ⊤) → A x)
⊤-ind A a ⋆ = a

-- rec = ind w/ constant target family
⊤-rec : (A : Set ℓ) → A → (⊤ → A) -- a = base case
⊤-rec A a ⋆ = ⊤-ind (λ _ → A) a ⋆

{-
  𝟘 (false)
-}

data ⊥ : Set where
𝟘 = ⊥

⊥-ind : (A : ⊥ → Set ℓ) → ((x : ⊥) → A x)
⊥-ind A ()

-- convenient
⊥-rec : (A : Set ℓ) → (⊥ → A)
⊥-rec A ()

¬ : Set ℓ → Set ℓ
¬ X = X → ⊥

{-
  product (AND)
-}

data _×_ (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  _,_ : A → B → A × B
infixr 2 _×_
infixr 4 _,_

×-ind : {A : Set ℓ₁} {B : Set ℓ₂}
      → (C : A × B → Set ℓ)
      → ((x : A) → (y : B) → C (x , y))
      → ((z : A × B) → C z)
×-ind C f (a , b) = f a b

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

＋-ind : {A : Set ℓ₁} {B : Set ℓ₂}
      → (C : A ＋ B → Set ℓ)
      → ((x : A) → C (inl x)) → ((y : B) → C (inr y))
      → ((z : A ＋ B) → C z)
＋-ind C ax ay (inl x) = ax x
＋-ind C ax ay (inr y) = ay y

{-
  dependent sum (there exists)
-}

data Σ {A : Set ℓ₁} (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  _,_ : (a : A) → B a → Σ B

Σ-ind : {A : Set ℓ₁} {B : A → Set ℓ₂}
      → (C : Σ B → Set ℓ)
      → ((x : A) (y : B x) → C (x , y))
      → ((z : Σ B) → C z)
Σ-ind C f (x , y) = f x y

pr₁ : {A : Set ℓ₁} {B : A → Set ℓ₂} → Σ B → A
pr₁ (x , y) = x

pr₂ : {A : Set ℓ₁} {B : A → Set ℓ₂} → (z : Σ B) → B (pr₁ z)
pr₂ (x , y) = y

-- \:4 ?? why agda
-Σ : (A : Set ℓ₁) (B : A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
-Σ A B = Σ B
syntax -Σ A (λ a → b) = Σ a ∶ A , b
infix 0 -Σ

{-
  dependent product (forall, implies)
-}

Π : {X : Set ℓ} (A : X → Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
Π{ℓ}{ℓ₁} {X} A = (x : X) → A x

-Π : (X : Set ℓ) (Y : X → Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
-Π X Y = Π Y
syntax -Π A (λ x → b) = Π x ꞉ A , b

id : {A : Set ℓ} → A → A
id a = a

_∘_ : {A : Set ℓ} {B : Set ℓ₁} {C : B → Set ℓ₂}
    → ((b : B) → C b) → (f : A → B) → ((x : A) → C (f x))
g ∘ h = λ x → g (h x)
infixr 5 _∘_

{-
  equality (equality)
-}

data _＝_ {A : Set ℓ} : A → A → Set ℓ where
  refl : (x : A) → x ＝ x
infix 4 _＝_

-- induction
ȷ : {A : Set ℓ} (C : (x y : A) → (x ＝ y) → Set ℓ₁)
  → ((x : A) → C x x (refl x))
  → (x y : A) (p : x ＝ y) → C x y p
ȷ C f x x (refl x) = f x

sym : {A : Set ℓ} {x y : A} → (x ＝ y) → (y ＝ x)
sym{ℓ} {A} {x}{y} p = ȷ (λ x y _ → y ＝ x) (λ x → refl x) x y p

trans : {A : Set ℓ} {x y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
trans{ℓ} {A} {x}{y}{z} p = ȷ (λ x y _ → y ＝ z → x ＝ z)
                             (λ x → (ȷ (λ x z _ → x ＝ z)
                                       (λ x → refl x)
                                       x z))
                             x y p

-- based path induction
ⅉ : {A : Set ℓ} (a : A) → (C : (x : A) → (x ＝ a) → Set ℓ₁)
  → C a (refl a)
  → (x : A) (p : x ＝ a) → C x p
ⅉ a C ca x (refl x) = ca
