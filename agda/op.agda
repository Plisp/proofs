{-# OPTIONS --without-K --exact-split --safe #-}

{-
  operator properties
-}

open import logic
open import path


assoc : {X : Set ℓ} → (X → X → X) → Set ℓ
assoc _·_ = ∀ a b c → (a · b) · c ＝ a · (b · c)

commut : {X : Set ℓ} → (X → X → X) → Set ℓ
commut _·_ = ∀ a b → a · b ＝ b · a

left-ac : {X : Set ℓ} → (_·_ : X → X → X) → assoc _·_ → commut _·_
        → (a b c : X) → a · (b · c) ＝ b · (a · c)
left-ac _·_ is-assoc is-commut a b c =
  begin                                   a · (b · c)
    =⟨ sym＝ (is-assoc a b c) ⟩            (a · b) · c
    =⟨ ap (λ e → e · c) (is-commut a b) ⟩ (b · a) · c
    =⟨ is-assoc b a c ⟩                   b · (a · c)
  ∎

right-ac : {X : Set ℓ} → (_·_ : X → X → X) → assoc _·_ → commut _·_
         → (a b c : X) → (a · b) · c ＝ (a · c) · b
right-ac _·_ is-assoc is-commut a b c =
  begin                                   (a · b) · c
    =⟨ is-assoc a b c ⟩                   a · (b · c)
    =⟨ ap (λ e → a · e) (is-commut b c) ⟩ a · (c · b)
    =⟨ sym＝ (is-assoc a c b) ⟩            (a · c) · b
  ∎

identity : {X : Set ℓ} → X → (X → X → X) → Set ℓ
identity e _·_ = ∀ x → (x · e ＝ x) × (e · x ＝ x)

has-inverse : {X : Set ℓ} → X → (X → X → X) → Set ℓ
has-inverse {X = X} e _·_ = ∀ x → Σ y ∶ X , (x · y ＝ e) × (y · x ＝ e)
