{-# OPTIONS --copatterns --guardedness #-}

open import logic
open import eq

variable B A R S : Set
variable E : Set → Set

mutual
  data itree-ind (E : Set → Set) (A R : Set) : Set where
    ret : R → itree-ind E A R
    tau : Itree E A R → itree-ind E A R
    vis : E A → (A → Itree E A R) → itree-ind E A R

  record Itree (E : Set → Set) (A R : Set) : Set where
    coinductive
    field
      alg : itree-ind E A R

  data wsim-ind (rel : itree-ind E A R → itree-ind E A R → Set) :
                itree-ind E A R → itree-ind E A R → Set where

    wsim-ret : (r : R) → wsim-ind rel (ret r) (ret r)

    wsim-ltau : {t t' : Itree E A R}
              → Wsim rel t t' → wsim-ind rel (tau t) (Itree.alg t')
    wsim-rtau : {t t' : Itree E A R}
              → Wsim rel t t' → wsim-ind rel (Itree.alg t) (tau t')

    wsim-vis : (e : E A) → (k k' : A → Itree E A R)
             → (∀ a → rel (Itree.alg (k a)) (Itree.alg (k' a)))
             → wsim-ind rel (vis e k) (vis e k')

  record Wsim {E : Set → Set} {A R : Set}
              (rel : itree-ind E A R → itree-ind E A R → Set)
              (a b : Itree E A R) : Set where
    coinductive
    field
      alg : wsim-ind rel (Itree.alg a) (Itree.alg b)

open Itree
open Wsim

Ret : R → Itree E A R
alg (Ret r) = ret r
Tau : Itree E A R → Itree E A R
alg (Tau t) = tau t
Vis : E A → (A → Itree E A R) → Itree E A R
alg (Vis e k) = vis e k

to-wsim : {a b : Itree E A R}
        → (rel : itree-ind E A R → itree-ind E A R → Set)
        → wsim-ind rel (alg a) (alg b) → Wsim rel a b
alg (to-wsim rel w) = w

wsim-eqtau : {t : Itree E A R} → Wsim _＝_ t t → wsim-ind _＝_ (tau t) (tau t)
wsim-eqtau wt = wsim-rtau (wsim-eqtau' wt)
  where
    wsim-eqtau' : {t : Itree E A R} → Wsim _＝_ t t → Wsim _＝_ (Tau t) t
    wsim-eqtau' wt = to-wsim _＝_ (wsim-ltau wt)

wsim-refl : {E : Set → Set} {A R : Set}
          → (t : Itree E A R) → Wsim _＝_ t t
alg (wsim-refl t) with (alg t)
...               | ret r = wsim-ret r
...               | tau t' = wsim-eqtau (wsim-refl t')
...               | vis e g = wsim-vis e g g (λ a → refl (alg (g a)))

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
