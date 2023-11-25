{-# OPTIONS --without-K --exact-split #-}

{-
  boolean stuff
-}

open import logic
open import types
open import equiv

data Bool : Set where
  true  : Bool
  false : Bool

𝟚 = 𝟙 ＋ 𝟙
𝟚-ind : (A : 𝟚 → Set ℓ) → A (inl ⋆) → A (inr ⋆) → ((b : 𝟚) → A b)
𝟚-ind A a₀ a₁ = ind＋ A
                (ind⊤ (λ (x : 𝟙) → (A (inl x))) a₀)
                (ind⊤ (λ (x : 𝟙) → (A (inr x))) a₁)

not : Bool → Bool
not true  = false
not false = true

_&&_ : Bool → Bool → Bool
true  && b = b
false && b = false

_||_ : Bool → Bool → Bool
true  || b = true
false || b = b

if_then_else : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

bool-𝟚-equivt : Bool ≃ 𝟚
bool-𝟚-equivt = quasi≃ (bool-to-𝟚 , 𝟚-to-bool ,
                        (λ { true → refl true ; false → refl false}) ,
                        (λ { (inl ⋆) → refl _ ; (inr ⋆) → refl _ }))
  where
    bool-to-𝟚 : Bool → 𝟚
    bool-to-𝟚 true  = inl ⋆
    bool-to-𝟚 false = inr ⋆

    𝟚-to-bool : 𝟚 → Bool
    𝟚-to-bool (inl _) = true
    𝟚-to-bool (inr _) = false
