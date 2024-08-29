{-# OPTIONS --without-K --exact-split --safe #-}

{-
  basic types
-}

open import logic

𝟚 = 𝟙 ＋ 𝟙

𝟚-ind : (A : 𝟚 → Set ℓ) → A (inl ⋆) → A (inr ⋆) → ((b : 𝟚) → A b)
𝟚-ind A a₀ a₁ = ind＋ A
                (ind⊤ (λ (x : 𝟙) → (A (inl x))) a₀)
                (ind⊤ (λ (x : 𝟙) → (A (inr x))) a₁)

{-
  natural numbers
-}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

indℕ : (A : ℕ → Set ℓ) → (A 0) → ((n : ℕ) → A n → A (suc n))
     → ((x : ℕ) → A x)
indℕ A a₀ s = h
  where
    h : (n : ℕ) → A n
    h 0       = a₀
    h (suc n) = s n (h n)

recℕ : {C : Set ℓ} → C → (ℕ → C → C) → (ℕ → C)
recℕ z f zero    = z
recℕ z f (suc n) = f n (recℕ z f n)

{-
  lists
-}

data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A
infixr 5 _∷_
{-# BUILTIN LIST List #-}


{-
  bounded index for integers below n
-}

data Fin : ℕ → Set where
  fz : {n : ℕ} → Fin (suc n)
  fs : {n : ℕ} → Fin n → Fin (suc n)

fmax : (n : ℕ) → Fin (suc n)
fmax 0       = fz
fmax (suc n) = fs (fmax n)

{-
  Martin-Löf's well-founded trees
-}

data W (A : Set) (B : A → Set) : Set where
  _◂_ : (s : A) → ((B s) → (W A B)) → (W A B)
