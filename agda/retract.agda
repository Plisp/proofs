{-# OPTIONS --without-K --exact-split --safe #-}

{-
  retracts: sections and retractions
-}

open import Agda.Primitive
open import logic
open import path
open import hlevel

{-
  retracts
-}

-- r ∘ s ＝ id , embedding then quotient , s ; r ＝ id
has-retraction : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
has-retraction {ℓ}{ℓ₁} {X}{Y} s = Σ r ∶ (Y → X) , r ∘ s ~ id

-- right inverse
has-section : {X : Set ℓ} {Y : Set ℓ₁} → (Y → X) → Set (ℓ ⊔ ℓ₁)
has-section {ℓ}{ℓ₁} {X}{Y} r = Σ s ∶ (X → Y) , r ∘ s ~ id

-- X type is a retract of Y
_◁_ : Set ℓ → Set ℓ₁ → Set (ℓ ⊔ ℓ₁)
X ◁ Y = Σ f ∶ (Y → X) , has-section f

retraction : {X : Set ℓ} {Y : Set ℓ₁} → X ◁ Y → (Y → X)
retraction (r , s , η) = r

section : {X : Set ℓ} {Y : Set ℓ₁} → X ◁ Y → (X → Y)
section (r , s , η) = s

is-retract : {X : Set ℓ} {Y : Set ℓ₁} → (p : X ◁ Y)
           → retraction p ∘ section p ~ id
is-retract (r , s , η) = η

refl◁ : (X : Set ℓ) → X ◁ X
refl◁ X = id , id , refl

_◁∙_ : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂} → X ◁ Y → Y ◁ Z → X ◁ Z
(r , s , η) ◁∙ (r' , s' , η') = r ∘ r' , s' ∘ s , λ x → ap r (η' (s x)) ∙ η x

_◁⟨_⟩_ : (X : Set ℓ) {Y : Set ℓ₁} {Z : Set ℓ₂} → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ x◁y ⟩ y◁z = x◁y ◁∙ y◁z
infixr 2 _◁⟨_⟩_

_◀ : (X : Set ℓ) → X ◁ X
X ◀ = refl◁ X
infix 3 _◀

-- a natural transformation between two fibrations
Nat : {X : Set ℓ} → (X → Set ℓ₁) → (X → Set ℓ₂) → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
Nat A B = ∀ x → A x → B x
-- gives a map between their total spaces
NatΣ : {X : Set ℓ} {A : X → Set ℓ₁} {B : X → Set ℓ₂} → Nat A B → Σ A → Σ B
NatΣ τ (x , a) = (x , τ x a)

Σ-retract : {X : Set ℓ} {A : X → Set ℓ₁} {B : X → Set ℓ₂}
          → ((x : X) → A x ◁ B x) → Σ A ◁ Σ B
Σ-retract {ℓ}{ℓ₁}{ℓ₂} {X} {A} {B} ρ = NatΣ r , NatΣ s , η
  where
    r = λ x → retraction (ρ x)
    s = λ x → section (ρ x)
    η' : (x : X) → r x ∘ s x ~ id
    η' x = is-retract (ρ x)

    η : NatΣ r ∘ NatΣ s ~ id
    η (x , a) = ap (λ - → (x , -)) (η' x a)

-- transport is an isomorphism
transport-is-retraction : {X : Set ℓ} (A : X → Set ℓ₁) {x y : X} (p : x ＝ y)
                        → transport A p ∘ transport A (sym＝ p) ~ id
transport-is-retraction A p = id~ (transport-p-sym p)

transport-is-section : {X : Set ℓ} (A : X → Set ℓ₁) {x y : X} (p : x ＝ y)
                     → transport A (sym＝ p) ∘ transport A p ~ id
transport-is-section A p = id~ (transport-sym-p p)

-- retraction similar to above but only at basepoints X ◁ Y =A Y=
Σ-reindex-retract : {X : Set ℓ} {Y : Set ℓ₁} {A : X → Set ℓ₂}
                  → (r : Y → X) → has-section r
                  → (Σ x ∶ X , A x) ◁ (Σ y ∶ Y , A (r y))
Σ-reindex-retract {ℓ}{ℓ₁}{ℓ₂} {X} {Y} {A} r (s , η) = ar , as , aη
  where
   ar : Σ (A ∘ r) → Σ A
   ar (y , a) = (r y , a)

   as : Σ A → Σ (A ∘ r) -- A (id x) -> A (r (s x))
   as (x , a) = (s x , transport A (sym＝ (η x)) a)

   -- to-Σ does a transport along the first equality which is cancelled
   aη : ((x , a) : Σ A) → (r (s x) , transport A (sym＝ (η x)) a) ＝ (x , a)
   aη (x , a) = to-Σ＝ (η x , transport-is-retraction A (η x) a)

--  Y    y  ← g x
--------    ⇊
--  X   f x ← f(g x) ← x
retract-of-singleton : {X : Set ℓ} {Y : Set ℓ₁}
                     → X ◁ Y → is-contr Y → is-contr X
retract-of-singleton (f , g , p) contr = f (center _ contr) , centered
  where
    centered : ∀ x → f (center _ contr) ＝ x
    centered x = ap f (centrality _ contr (g x)) ∙ (p x)
