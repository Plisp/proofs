{-# OPTIONS --copatterns --guardedness #-}

open import Agda.Primitive

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data 𝟙 : Set where
  ⋆ : 𝟙

mutual
  record Ret (R : Set) : Set where
    field
      r : R

  record Tau (E : Set → Set) (R : Set) : Set₁ where
    coinductive
    field
      t : Itree E R

  record Vis (E : Set → Set) (A R : Set) : Set₁ where
    coinductive
    field
      e : E A
      k : A → Itree E R

  data Itree (E : Set → Set) (R : Set) : Set₁ where
    ret' : Ret R → Itree E R
    tau' : Tau E R → Itree E R
    vis' : {A : Set} → Vis E A R → Itree E R

data IO : Set → Set where
  input : IO ℕ
  output : ℕ → IO 𝟙

mutual
  spintau : Tau IO 𝟙
  Tau.t spintau = spin

  spin : Itree IO 𝟙
  spin = tau' spintau

  vis-inst : {A R : Set} {E : Set → Set} → E A → (A → Itree E R) → Vis E A R
  Vis.e (vis-inst e k) = e
  Vis.k (vis-inst e k) = k

  vis : {A R : Set} {E : Set → Set} → E A → (A → Itree E R) → Itree E R
  vis e k = vis' (vis-inst e k)

  echo-in-vis : Vis IO ℕ 𝟙
  Vis.e echo-in-vis = input
  Vis.k echo-in-vis = λ x → vis' (echo-out-vis x)

  echo-out-vis : (x : ℕ) → Vis IO 𝟙 𝟙
  Vis.e (echo-out-vis x) = output x
  Vis.k (echo-out-vis x) = λ _ → echo

  echo : Itree IO 𝟙
  echo = vis input (λ x → (vis (output x) (λ _ → echo)))

  -- trigger-vis : {E : Set → Set}

  -- trigger : (E : Set → Set) {A : Set} (e : E A) → Itree E A
  -- trigger E e = vis' trigger-vis vis' e (λ x → (ret' x))

-- bind : {E : Set → Set} {R S : Set} (t : Itree E R) (k : R → Itree E S) → Itree E S
-- bind (ret' r) k  = k r
-- bind (tau' t) k  = tau' (♯ (bind (♭ t) k))
-- bind (vis' e k') k  = vis' e (λ x → ♯ (bind (♭ (k' x)) k))
