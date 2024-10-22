{-# OPTIONS --without-K --exact-split --safe #-}

{-
  univalence
-}

open import Agda.Primitive
open import logic
open import path
open import equiv

idtoeq : (X Y : Set ℓ) → X ＝ Y → X ≃ Y
idtoeq X X (refl X) = refl≃ X

{-
  ua is the other direction
-}

is-univalent : (ℓ : Level) → Set (lsuc ℓ)
is-univalent ℓ = ∀ (X Y : Set ℓ) → is-equivalence (idtoeq X Y)

univalence-≃ : is-univalent ℓ → (X Y : Set ℓ) → (X ＝ Y) ≃ (X ≃ Y)
univalence-≃ univalence X Y = idtoeq X Y , univalence X Y

ua : is-univalent ℓ → (X Y : Set ℓ) → X ≃ Y → X ＝ Y
ua univalence X Y = inverse (idtoeq X Y) (univalence X Y)

ua-transport : {X Y : Set ℓ} → X ＝ Y → X → Y
ua-transport {X = X} {Y} p = pr₁ (idtoeq X Y p)

{-
  examples TODO
-}
