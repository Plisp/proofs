{-# OPTIONS --copatterns --guardedness #-}

open import Function.Base using (case_of_; case_return_of_)
open import logic
open import eq

mutual
  data itree-ind (E : Set → Set) (A R : Set) : Set₁ where
    ret : R → itree-ind E A R
    tau : Itree E A R → itree-ind E A R
    vis : E A → (A → Itree E A R) → itree-ind E A R

  record Itree (E : Set → Set) (A R : Set) : Set₁ where
    coinductive
    field
      alg : itree-ind E A R

open Itree

Ret : {E : Set → Set} {A R : Set} → R → Itree E A R
alg (Ret r) = ret r

Tau : {E : Set → Set} {A R : Set} → Itree E A R → Itree E A R
alg (Tau t) = tau t

Vis : {E : Set → Set} {A R : Set} → E A → (A → Itree E A R) → Itree E A R
alg (Vis e k) = vis e k

trigger : {E : Set → Set} {A : Set} (e : E A) → Itree E A A
trigger e = Vis e (λ x → Ret x)

-- algebra (Itree E A R) × ktree
-- (Ret r,   k).ret = ???
-- (Tau t,   k).tau = (t,k)
-- (Vis e g, k).vis = vis e λx.((g x),k) A -> X --bind ∘-> A -> Y
bind : {E : Set → Set} {A R S : Set}
     → Itree E A R → (R → itree-ind E A S)
     → Itree E A S
alg (bind t k) with alg t
...            | ret r = (k r)
...            | tau t = tau (bind t k)
...            | vis e g = vis e (λ x → bind (g x) k)

iter : {E : Set → Set} {A B R : Set}
     → (A → Itree E A (A ＋ B))
     → A → Itree E A B
alg (iter body a) = alg (bind (body a)
                         λ { (inl a) → tau (iter body a)
                           ; (inr b) → ret b
                         }
                    )

-- spin
spin : Itree (λ x → 𝟙) 𝟙 𝟙
alg spin = tau spin

-- TODO need bisimulation as setoid equivalence for everything
