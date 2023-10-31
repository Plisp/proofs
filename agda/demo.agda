{-
  agda file for wednesday
-}

open import logic
open import paths
open import types
open import arith

-- tail-recursive (factorial 9) is faster: C-c C-n normalize (code extraction)
slow-factorial : ℕ → ℕ
slow-factorial 0 = 1
slow-factorial (suc n) = suc n * slow-factorial n

-- C-c C-c to split on variable
fact-iter : ℕ → ℕ → ℕ
fact-iter zero    acc = acc
fact-iter (suc n) acc = fact-iter n (suc n * acc)

-- it is essential that all terms terminate, otherwise things get inconsistent
-- a : ⊥ = a, f(x) = f(x) + 1 → (0 ＝ 1)
-- lexicographic: find an ordering on argument 'strings' that decreases
ackermann : ℕ → ℕ → ℕ
ackermann 0 b = suc b
ackermann (suc a) b = {!!}
-- ackermann (suc a) 0 = ackermann a 1
-- ackermann (suc a) (suc b) = ackermann a (ackermann (suc a) b)



-- factorial
factorial : ℕ → ℕ
factorial n = fact-iter n 1

-- computation rules: .simps/rules are builtin to the metatheory ≡ external equality
-- internal propositional equality ＝ is for things which we do not define to be true
compute-3-factorial : (factorial 3) ＝ 6
compute-3-factorial = refl _



-- proof
fact-commut-mult : (n k acc : ℕ) → fact-iter n (k * acc) ＝ k * fact-iter n acc
fact-commut-mult zero    k acc = refl _
fact-commut-mult (suc n) k acc =
  begin fact-iter (suc n) (k * acc)
    =⟨ {!!} ⟩ k * fact-iter (suc n) acc
  ∎

fact-lemma : (n acc : ℕ) → fact-iter (suc n) acc ＝ suc n * fact-iter n acc
fact-lemma zero    acc = refl _
fact-lemma (suc n) acc =
  begin fact-iter (suc (suc n)) acc
    =⟨ {!!} ⟩ suc (suc n) * fact-iter (suc n) acc
  ∎

factorial-rec : (n : ℕ) → factorial (suc n) ＝ (suc n) * factorial n
factorial-rec zero    = refl _
factorial-rec (suc n) = fact-lemma (suc n) 1

{-
  fib
-}

-- fib : ℕ → ℕ
-- fib 0 = 1
-- fib (suc (suc a)) = fib a + fib (suc a)

{-
  choice
-}
open import Agda.Primitive
open import hott

choice-theorem : (X : Set ℓ) (A : X → Set ℓ₁)
               → (R : (x : X) → A x → Set ℓ₂)
               → ((x : X) → Σ a ∶ A x , R x a)
               → Σ f ∶ Π A , ((x : X) → R x (f x))

choice-theorem X A R s = f , φ
 where
  f : (x : X) → A x
  f x = {!!}

  φ : (x : X) → R x (f x)
  φ x = {!!}
