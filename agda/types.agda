open import logic

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
    h 0 = a₀
    h (suc n) = s n (h n)

ℕ-rec : (A : Set ℓ) → A → (ℕ → A → A) → (ℕ → A)
ℕ-rec A a₀ s = ℕ-ind (λ _ → A) a₀ s

pred : ℕ → ℕ
pred n = snd (pred' n) where
         pred' : ℕ → ℕ × ℕ
         pred' zero = (zero , zero)
         pred' (suc n) = (suc (fst (pred' n)) , fst (pred' n))

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

data WNatB : Bool → Set where
  wleft  : ⊥ → WNatB false
  wright : ⊤ → WNatB true

WNat : Set
WNat = W Bool WNatB

wzero : WNat
wzero = false ◂ (λ {(wleft ())})

wsuc : WNat → WNat
wsuc n = true ◂ (λ _ → n)

wrec : {C : Set} → WNat → C → (WNat → C → C) → C
wrec (false ◂ _) z _ = z
wrec (true  ◂ f) z s = s (f (wright ⋆)) (wrec (f (wright ⋆)) z s)
