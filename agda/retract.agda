{-# OPTIONS --without-K --exact-split --safe #-}

{-
  retracts: sections and retractions
-}

open import Agda.Primitive
open import logic
open import types
open import function
open import functor
open import path
open import homotopy
open import hlevel

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

{-
  lower hlevels closed under retraction
-}

--  Y    y  ← g x
--------    ⇊
--  X   f x ← f(g x) ← x
retract-of-singleton : {X : Set ℓ} {Y : Set ℓ₁}
                     → X ◁ Y → is-contr Y → is-contr X
retract-of-singleton (f , g , η) contr = f (center _ contr) , centered
  where
    centered : ∀ x → f (center _ contr) ＝ x
    centered x = ap f (centrality contr (g x)) ∙ (η x)

-- retraction enables equality cancellation
-- originally devised for the invertible to equiv proof
rap : {X : Set ℓ} {Y : Set ℓ₁} {x y : X} (f : X → Y)
    → has-retraction f → (f x ＝ f y) → (x ＝ y)
rap {ℓ}{ℓ₁}{X}{Y} {x}{y} f (g , gf) p = sym＝ (gf x) ∙ (ap g p) ∙ gf y

rap-ap : {X : Set ℓ} {Y : Set ℓ₁} {x y : X} {f : X → Y}
       → (r : has-retraction f) (p : x ＝ y)
       → rap f r (ap f p) ＝ p
rap-ap {ℓ}{ℓ₁}{X}{Y} {x}{y} (g , gf) (refl x)
  = ap (λ e → sym＝ (gf x) ∙ e) (sym＝ (p＝refl∙p (gf x))) ∙ iv∙p＝refl (gf x)

retract-of-subsingleton : {X : Set ℓ} {Y : Set ℓ₁}
                        → X ◁ Y → is-subsingleton Y → is-subsingleton X
retract-of-subsingleton (g , f , η) ss x1 x2 = rap f (g , η) (ss (f x1) (f x2))

retract-of-hlevel : {X : Set ℓ} {Y : Set ℓ₁} (n : ℕ)
                  → X ◁ Y → Y is-of-hlevel n → X is-of-hlevel n
retract-of-hlevel 0 r hf = retract-of-singleton r hf
retract-of-hlevel (suc n) (g , f , η) hf x x'
  = retract-of-hlevel n (rap f (g , η) , ap f , rap-ap (g , η)) (hf (f x) (f x'))

-- retract-of-hlevel : {X : Set ℓ} {Y : Set ℓ₁} (n : ℕ)
--                   → X ◁ Y → Y is-of-hlevel n → X is-of-hlevel n
-- retract-of-hlevel 0 r hf = retract-of-singleton r hf
-- retract-of-hlevel 1 r hf -- coercion between equivalent formulations
--   = subsingleton-hlevel1 (retract-of-subsingleton r (hlevel1-subsingleton hf))
-- retract-of-hlevel (suc (suc n)) (g , f , η) hf x x' p q
--   = retract-of-hlevel n (rap (ap f) test , ap (ap f) , rap-ap test)
--                       (hf (f x) (f x') (ap f p) (ap f q))
--   where
--     test : has-retraction (ap f)
--     test = (rap f (g , η) , rap-ap (g , η))
