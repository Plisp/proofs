{-# OPTIONS --without-K --exact-split --safe #-}

{-
  basic data structures
-}

open import logic
open import path

data Bool : Set where
  true  : Bool
  false : Bool

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

recℕ : {C : Set} → C → (ℕ → C → C) → (ℕ → C)
recℕ z f zero    = z
recℕ z f (suc n) = f n (recℕ z f n)

plus : ℕ → ℕ → ℕ  -- 0-plus and vv a-plus → a+1 plus
plus = recℕ (λ b → b) (λ a plus-a → λ b → suc (plus-a b))

-- peano +
_+_ : ℕ → ℕ → ℕ
zero    + b = b
(suc a) + b = suc (a + b)
infix 7 _+_

_*_ : ℕ → ℕ → ℕ
zero    * b = 0
(suc a) * b = (a * b) + b
infix 8 _*_

_≤_ _≥_ : ℕ → ℕ → Set
0 ≤ y     = 𝟙
suc x ≤ 0     = 𝟘
suc x ≤ suc y = x ≤ y

x ≥ y = y ≤ x
infix 4 _≤_ _≥_

suc-x≠0 : (x : ℕ) → suc x ≠ 0 -- peano axiom, note pattern lambda!
suc-x≠0 _ p = 𝟙≠𝟘 (ap (λ { 0 → 𝟘 ; (suc _) → 𝟙 }) p)

{-
  lists
-}

data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A
infixr 5 _∷_
{-# BUILTIN LIST List #-}

-- bounded index for integers below n
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
