{-# OPTIONS --without-K --exact-split --safe #-}

{-
  conversion from joyal equivs
-}

open import Agda.Primitive
open import logic
open import path
open import homotopy
open import retract
open import equiv

is-joyal-equiv : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
is-joyal-equiv f = has-section f × has-retraction f

joyal-equivs-are-invertible : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                            → is-joyal-equiv f → invertible f
joyal-equivs-are-invertible f ((s , ps) , (r , pr))
  = r , pr , λ x → ap f (one-up-to-homotopy x) ∙ ps x
  where
    one-up-to-homotopy : r ~ s
    one-up-to-homotopy x = sym＝ (ap r (ps x)) ∙ pr (s x)

invertibles-are-joyal-equivs : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                             → invertible f → is-joyal-equiv f
invertibles-are-joyal-equivs f (g , s , r) = (g , r) , g , s

joyal-equivs-are-equivs : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                        → is-joyal-equiv f → is-equivalence f
joyal-equivs-are-equivs f e = invertibles-are-equivalences f
                                (joyal-equivs-are-invertible f e)

equivs-are-joyal-equivs : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                        → is-equivalence f → is-joyal-equiv f
equivs-are-joyal-equivs f e = invertibles-are-joyal-equivs f
                                (equivalences-are-invertible f e)
