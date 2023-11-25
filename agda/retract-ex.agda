{-# OPTIONS --without-K --exact-split --safe #-}

{-
  examples of retracts
-}

open import Agda.Primitive
open import logic
open import path
open import functor using (NatΣ)
open import homotopy
open import retract

-- transport is an isomorphism
transport-is-retraction : {X : Set ℓ} (A : X → Set ℓ₁) {x y : X} (p : x ＝ y)
                        → transport A p ∘ transport A (sym＝ p) ~ id
transport-is-retraction A p = id~ (transport-p-sym p)

transport-is-section : {X : Set ℓ} (A : X → Set ℓ₁) {x y : X} (p : x ＝ y)
                     → transport A (sym＝ p) ∘ transport A p ~ id
transport-is-section A p = id~ (transport-sym-p p)

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

sections-homotopy-closed : {X : Set ℓ} {Y : Set ℓ₁} (f g : X → Y)
                         → has-retraction f
                         → g ~ f
                         → has-retraction g
sections-homotopy-closed f g (r , p) g~f = r , λ x → ap r (g~f x) ∙ p x

retractions-homotopy-closed : {X : Set ℓ} {Y : Set ℓ₁} (f g : X → Y)
                            → has-section f
                            → g ~ f
                            → has-section g
retractions-homotopy-closed f g (s , p) g~f = s , λ x → g~f (s x) ∙ p x
