{-# OPTIONS --without-K --exact-split --safe #-}

{-
  boolean stuff
-}

open import logic
open import types

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

if_then_else : {A : Set ℓ} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y
