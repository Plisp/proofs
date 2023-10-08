{-# OPTIONS --copatterns --guardedness #-}

open import Agda.Primitive

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data 𝟙 : Set where
  ⋆ : 𝟙

mutual
  data itree-ind (E : Set → Set) (A R : Set) : Set₁ where
    Ret : R → itree-ind E A R
    Tau : Itree E A R → itree-ind E A R
    Vis : (A → Itree E A R) → itree-ind E A R

  record Itree (E : Set → Set) (A R : Set) : Set₁ where
    coinductive
    field
      alg : itree-ind E A R

data IO : Set → Set where
  input : IO ℕ
  output : ℕ → IO 𝟙

mutual
  spin : Itree (λ x → 𝟙) 𝟙 𝟙
  Itree.alg spin = Tau spin
