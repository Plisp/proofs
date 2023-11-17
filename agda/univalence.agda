{-# OPTIONS --without-K --exact-split --safe #-}

{-
  univalence
-}

open import Agda.Primitive
open import logic
open import path
open import equiv

_≃_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
X ≃ Y = Σ f ∶ (X → Y) , is-equivalence f
infix 5 _≃_

equiv-fn : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → X → Y
equiv-fn (f , i) = f

equiv-proof : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → X → Y
equiv-proof (f , i) = f

refl≃ : (X : Set ℓ) → X ≃ X
refl≃ X = id , id-is-equivalence X

_●_ : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂} → X ≃ Y → Y ≃ Z → X ≃ Z
(f , d) ● (f' , e) = f' ∘ f , equivalence-∘ e d
trans≃ = _●_

sym≃ : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → Y ≃ X
sym≃ (f , e) = inverse f e , inverse-is-equivalence e

_≃⟨_⟩_ : (X : Set ℓ) {Y : Set ℓ₁} {Z : Set ℓ₂} → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e
infixr 2 _≃⟨_⟩_

_■ : (X : Set ℓ) → X ≃ X
_■ = refl≃
infix 3 _■

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
ua-transport {ℓ} {X} {Y} p = equiv-fn (idtoeq X Y p)

{-
  conversion
-}

quasi-equiv : (A : Set ℓ) (B : Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
quasi-equiv A B = Σ f ∶ (A → B) , invertible f

invertible-to-≃ : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                → invertible f → X ≃ Y
invertible-to-≃ f i = f , invertibles-are-equivalences f i

{-
  TODO examples
-}
