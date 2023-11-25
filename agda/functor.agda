{-# OPTIONS --without-K --exact-split --safe #-}

{-
  category related properties
-}

open import Agda.Primitive
open import logic
open import path

-- a natural transformation between two fibrations
Nat : {X : Set ℓ} → (X → Set ℓ₁) → (X → Set ℓ₂) → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
Nat A B = ∀ x → A x → B x

Nats-are-natural : {X : Set ℓ} (A : X → Set ℓ₁) (B : X → Set ℓ₂) (τ : Nat A B)
                 → {x y : X} (p : x ＝ y)
                 → τ y ∘ transport A p ＝ transport B p ∘ τ x
Nats-are-natural A B τ (refl x) = refl (τ x)

-- gives a map between their total spaces
NatΣ : {X : Set ℓ} {A : X → Set ℓ₁} {B : X → Set ℓ₂} → Nat A B → Σ A → Σ B
NatΣ τ (x , a) = (x , τ x a)

{-
  functorial liftings
-}

f× : {W : Set ℓ} {X : Set ℓ₁} {Y : Set ℓ₂} {Z : Set ℓ₃}
   → (W → Y) → (X → Z)
   → (W × X) → (Y × Z)
f× f g (a , b) = f a , g b

f＋ : {W : Set ℓ} {X : Set ℓ₁} {Y : Set ℓ₂} {Z : Set ℓ₃}
   → (W → Y) → (X → Z)
   → (W ＋ X) → (Y ＋ Z)
f＋ f g = ind＋ _ (inl ∘ f) (inr ∘ g)
