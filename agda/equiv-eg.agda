{-# OPTIONS --without-K --exact-split --safe #-}

{-
  examples
-}

open import Agda.Primitive
open import logic
open import path
open import hlevel
open import retract
open import equiv

quasi-equiv : (A : Set ℓ) (B : Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
quasi-equiv A B = Σ f ∶ (A → B) , invertible f

transport-is-equiv : {X : Set ℓ} (A : X → Set ℓ₁) {x y : X} (p : x ＝ y)
                   → is-equivalence (transport A p)
transport-is-equiv A p = invertibles-are-equivalences (transport A p)
                           (transport A (sym＝ p) ,
                           transport-is-section A p ,
                           transport-is-retraction A p)

◁≃ : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → X ◁ Y
◁≃ (f , e) = inverse f e , f , inverses-are-retractions f e

≃▷ : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → Y ◁ X
≃▷ (f , e) = f , inverse f e , inverses-are-sections f e

equiv-to-singleton : {X : Set ℓ} {Y : Set ℓ₁}
                   → X ≃ Y → is-contr Y → is-contr X
equiv-to-singleton e =  retract-of-singleton (◁≃ e)
