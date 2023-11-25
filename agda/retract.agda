{-# OPTIONS --without-K --exact-split --safe #-}

{-
  retracts: sections and retractions
-}

open import Agda.Primitive
open import logic
open import types using (ℕ;zero;suc)
open import path
open import homotopy
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
    centered x = ap f (centrality _ contr (g x)) ∙ (η x)

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
