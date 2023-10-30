{-# OPTIONS --copatterns --guardedness #-}

open import logic
open import paths

variable B A R S : Set
variable E : Set → Set

mutual
  data itree-ind (E : Set → Set) (A R : Set) : Set where
    ret : R → itree-ind E A R
    tau : Itree E A R → itree-ind E A R
    vis : E A → (A → Itree E A R) → itree-ind E A R

  record Itree (E : Set → Set) (A R : Set) : Set where
    coinductive
    constructor alg'
    field
      alg : itree-ind E A R

  Ret : R → Itree E A R
  Itree.alg (Ret r) = ret r
  Tau : Itree E A R → Itree E A R
  Itree.alg (Tau t) = tau t
  Vis : E A → (A → Itree E A R) → Itree E A R
  Itree.alg (Vis e k) = vis e k

  data wsim-ind (rel : Itree E A R → Itree E A R → Set) :
                Itree E A R → Itree E A R → Set where

    wsim-ret : (r : R) → wsim-ind rel (Ret r) (Ret r)

    wsim-ttau : {t t' : Itree E A R}
              → rel t t' → wsim-ind rel (Tau t) (Tau t')
    wsim-ltau : {t t' : Itree E A R}
              → Wsim rel t t' → wsim-ind rel (Tau t) t'
    wsim-rtau : {t t' : Itree E A R}
              → Wsim rel t t' → wsim-ind rel t (Tau t')

    wsim-vis : (e : E A) → (k k' : A → Itree E A R)
             → (∀ a → rel (k a) (k' a))
             → wsim-ind rel (Vis e k) (Vis e k')

  record Wsim {E : Set → Set} {A R : Set}
              (rel : Itree E A R → Itree E A R → Set)
              (a b : Itree E A R) : Set where
    coinductive
    constructor alg'
    field
      alg : wsim-ind rel a b

open Itree
open Wsim

{-# ETA Wsim #-}
-- ret-lem : (t : Itree E A R) → (r : R) → ret r ＝ (alg t) → Ret r ＝ t
-- ret-lem t r p = ap alg' p

wsim-refl : {E : Set → Set} {A R : Set}
          → (t : Itree E A R) → Wsim _＝_ t t
alg (wsim-refl t) with (alg t)
...               | ret r = wsim-ret r
...               | tau t' = ?
...               | vis e g = ? -- wsim-vis e g g (λ a → refl (alg (g a)))

{-
  combinators
-}

-- algebra (Itree E A R) × ktree
-- non-corec returns can be considered as an A + I (id) algebra map
bind : Itree E A R → (R → itree-ind E A S) → Itree E A S
alg (bind t k) with alg t
...            | ret r = (k r)
...            | tau t = tau (bind t k)
...            | vis e g = vis e (λ x → bind (g x) k)

iter : {E : Set → Set} {A S B : Set}
     → (S → Itree E A (S ＋ B)) → S → Itree E A B
iter {E}{A}{S}{B} body s = iter' (body s) where
  iter' : Itree E A (S ＋ B) → Itree E A B
  alg (iter' t) with alg t
  ...           | ret (inl s) = tau (iter' (body s))
  ...           | ret (inr v) = ret v
  ...           | tau u = tau (iter' u)
  ...           | vis e g = vis e (λ x → iter' (g x))

{-
  examples
-}

trigger : (e : E A) → Itree E A A
trigger e = Vis e (λ x → Ret x)

-- spin
spin : Itree (λ x → 𝟙) 𝟙 𝟙
alg spin = tau spin
