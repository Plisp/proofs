{-# OPTIONS --without-K --exact-split #-}

{-
  lists and maybe vectors
-}

open import logic
open import types
open import path
open import arith

{-
  functor laws
-}

map : {A B : Set} (f : A → B) → List A → List B
map f []        = []
map f (a ∷ as) = (f a) ∷ (map f as)

map-id : {A : Set} (xs : List A) → (map id xs) ＝ xs
map-id [] = refl _
map-id (x ∷ xs) =
  begin
                               map id (x ∷ xs)
    =⟨⟩                        (id x) ∷ (map id xs)
    =⟨⟩                        x ∷ (map id xs)
    =⟨ ap (x ∷_) (map-id xs) ⟩ x ∷ xs
  ∎

map-compose : {A B C : Set} (f : B → C) (g : A → B) (xs : List A)
            → map (f ∘ g) xs ＝ map f (map g xs)
map-compose f g [] =
  begin map (f ∘ g) []
    =⟨⟩ []
    =⟨⟩ map f []
    =⟨⟩ map f (map g [])
  ∎
map-compose f g (x ∷ xs) =
  begin
                                              map (f ∘ g) (x ∷ xs)
    =⟨⟩                                       (f ∘ g) x ∷ map (f ∘ g) xs
    =⟨⟩                                       f (g x) ∷ map (f ∘ g) xs
    =⟨ ap (f (g x) ∷_) (map-compose f g xs) ⟩ f (g x) ∷ map f (map g xs)
    =⟨⟩                                       map f ((g x) ∷ map g xs)
    =⟨⟩                                       map f (map g (x ∷ xs))
  ∎

{-
  bounded vectors
-}

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

length : {A : Set} {n : ℕ} → Vec A n → ℕ
length {_} {n} _ = n

_!!_ : {A : Set} {n : ℕ} → Vec A n → Fin n → A
(a ∷ as) !! fz   = a
(a ∷ as) !! fs b = as !! b

_++_ : {A : Set} {x y : ℕ} → Vec A x → Vec A y → Vec A (x + y)
[]       ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
