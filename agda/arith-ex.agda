{-# OPTIONS --without-K --exact-split --safe #-}

{-
  arithmetic
-}

open import logic
open import types
open import path
open import op
open import hlevel
open import arith

ackermann : ℕ → ℕ → ℕ
ackermann = recℕ mzero msucc
  where
    mzero : ℕ → ℕ
    mzero = λ n → suc n
    -- from ackermann m _, produce ackermann (suc m) _
    msucc : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
    msucc = λ m am → recℕ (am 1) (λ n a-sm-n → am a-sm-n)

ind≤ : (A : {n m : ℕ} → (p : n ≤ m) → Set)
     → (∀ {n : ℕ} → (p : zero ≤ n) → A p)
     → (∀ {m n : ℕ} → (p : m ≤ n) → A p → A (s≤s p))
     → (m n : ℕ) → (p : m ≤ n) → A p
ind≤ A zn ss n m z≤n = zn z≤n
ind≤ A zn ss n m (s≤s p) = ss p (ind≤ A zn ss (pred n) (pred m) p)

trans'-≤ : (l m n : ℕ) → (l ≤ m) → (m ≤ n) → (l ≤ n)
trans'-≤ l m n lm mn = ind-lm n mn
  where
    ≤-dest : ∀ {m n} → suc m ≤ suc n → m ≤ n -- uniqueness is inversion
    ≤-dest {m} {n} (s≤s p) = p

    ind-mn : {l m : ℕ} → (l ≤ m)
           → (∀ n → (m ≤ n) → (l ≤ n))
           → (n : ℕ) → (suc m ≤ n) → (suc l ≤ n)
    -- definitional match  vvv
    ind-mn {l} {m} _ mnln (suc n) sm≤n = s≤s (mnln n (≤-dest sm≤n))

    ind-lm : (n : ℕ) → (m ≤ n) → (l ≤ n)
    ind-lm = ind≤ (λ {l' m' : ℕ} → λ (lm : l' ≤ m') -- need forall n
                                 → ∀ (n : ℕ) → (m' ≤ n) → (l' ≤ n))
                  (λ _ → λ _ _ → z≤n) ind-mn l m lm
