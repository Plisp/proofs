{-# OPTIONS --without-K --exact-split --safe #-}
open import logic
open import eq

{-
  basic data structures
-}

-- booleans
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

-- natural numbers
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

ℕ-ind : (A : ℕ → Set ℓ) → (A 0) → ((n : ℕ) → A n → A (suc n))
      → ((x : ℕ) → A x)
ℕ-ind A a₀ s = h
  where
    h : (n : ℕ) → A n
    h 0       = a₀
    h (suc n) = s n (h n)

ℕ-rec : (A : Set ℓ) → A → (ℕ → A → A) → (ℕ → A)
ℕ-rec A a₀ s = ℕ-ind (λ _ → A) a₀ s

-- peano +
_+_ : ℕ → ℕ → ℕ
zero    + b = b
(suc a) + b = suc (a + b)

_*_ : ℕ → ℕ → ℕ
zero    * b = 0
(suc a) * b = (a * b) + b

_≤_ _≥_ : ℕ → ℕ → Set
0     ≤ y     = 𝟙
suc x ≤ 0     = 𝟘
suc x ≤ suc y = x ≤ y

x ≥ y = y ≤ x
infix 4 _≤_ _≥_

-- peano axiom, note pattern lambda!
suc-neq-zero : (x : ℕ) → suc x ≠ 0
suc-neq-zero _ p = 𝟙-neq-𝟘 (ap (λ { 0 → 𝟘 ; (suc _) → 𝟙 }) p)

-- lists
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
fmax zero = fz
fmax (suc n) = fs (fmax n)

-- Martin-Löf's well-founded trees
data W (A : Set) (B : A → Set) : Set where
  _◂_ : (s : A) → ((B s) → (W A B)) → (W A B)
