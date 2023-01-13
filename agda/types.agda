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
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero    + b = b
(suc a) + b = suc (a + b)

_*_ : ℕ → ℕ → ℕ
zero    * b = zero
(suc a) * b = b + (a * b)

pred : ℕ → ℕ
pred n = snd (pred' n) where
         pred' : ℕ → ℕ × ℕ
         pred' zero = zero , zero
         pred' (suc n) = suc (fst (pred' n)) , fst (pred' n)

-- lists
data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A
infixr 5 _::_

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

_++_ : {A : Set} {x y : ℕ} → Vec A x → Vec A y → Vec A (x + y)
[]        ++ bs = bs
(a :: as) ++ bs = a :: (as ++ bs)

append : {A : Set} {n : ℕ} → (x : A) → Vec A n → Vec A (suc n)
append x []        = x :: []
append x (a :: as) = a :: (append x as)

iota : (n : ℕ) → Vec ℕ n
iota zero    = []
iota (suc n) = append n (iota n)

head : {A : Set} {n : ℕ} → Vec A (suc n) → A
head (a :: as) = a

tail : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A n
tail (a :: as) = as

map : {A B : Set} {n : ℕ} → (f : A → B) → Vec A n → Vec B n
map f []        = []
map f (a :: as) = (f a) :: (map f as)

length : {A : Set} {n : ℕ} → Vec A n → ℕ
length {_} {n} _ = n

-- bounded index for integers below n
data Fin : ℕ → Set where
  fz : {n : ℕ} → Fin (suc n)
  fs : {n : ℕ} → Fin n → Fin (suc n)

_!!_ : {A : Set} {n : ℕ} → Vec A n → Fin n → A
(a :: as) !! fz   = a
(a :: as) !! fs b = as !! b

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
wrec (true  ◂ f) z s = s (f (wright ⟨⟩)) (wrec (f (wright ⟨⟩)) z s)
