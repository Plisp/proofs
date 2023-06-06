{-# OPTIONS --without-K --exact-split --safe #-}

{-
  operator properties
-}

open import logic
open import eq

op-assoc : {X : Set ℓ} → (X → X → X) → Set ℓ
op-assoc _·_ = ∀ a b c → (a · b) · c ＝ a · (b · c)

op-commut : {X : Set ℓ} → (X → X → X) → Set ℓ
op-commut _·_ = ∀ a b → a · b ＝ b · a

op-id : {X : Set ℓ} → X → (X → X → X) → Set ℓ
op-id e _·_ = ∀ x → (x · e ＝ x) × (e · x ＝ x)

op-inverse : {X : Set ℓ} → X → (X → X → X) → Set ℓ
op-inverse{ℓ} {X} e _·_ = ∀ x → Σ y ꞉ X , (x · y ＝ e) × (y · x ＝ e)
