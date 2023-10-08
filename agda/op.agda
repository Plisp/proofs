{-# OPTIONS --without-K --exact-split --safe #-}

{-
  operator properties
-}

open import logic
open import eq
open import hott

assoc : {X : Set ℓ} → (X → X → X) → Set ℓ
assoc _·_ = ∀ a b c → (a · b) · c ＝ a · (b · c)

commut : {X : Set ℓ} → (X → X → X) → Set ℓ
commut _·_ = ∀ a b → a · b ＝ b · a

identity : {X : Set ℓ} → X → (X → X → X) → Set ℓ
identity e _·_ = ∀ x → (x · e ＝ x) × (e · x ＝ x)

a-inverse : {X : Set ℓ} → X → (X → X → X) → Set ℓ
a-inverse{ℓ} {X} e _·_ = ∀ x → Σ y ∶ X , (x · y ＝ e) × (y · x ＝ e)
