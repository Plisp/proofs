{-
  solutions to wednesday
-}

open import logic
open import paths
open import types
open import arith

fact-iter : ℕ → ℕ → ℕ
fact-iter zero    acc = acc
fact-iter (suc n) acc = fact-iter n (suc n * acc)

factorial : ℕ → ℕ
factorial n = fact-iter n 1

fact-commut-mult : (n k acc : ℕ) → fact-iter n (k * acc) ＝ k * fact-iter n acc
fact-commut-mult zero    k acc = refl _
-- IH : fact-iter n k*acc ＝ k * fact-iter n acc
-- fact-iter Sn k*acc = fact-iter n (Sn * (k * acc))
--                   [ smh.. now I have to develop arithmetic theory
-- fact-iter Sn k*acc = fact-iter n ((Sn * k) * acc)
-- fact-iter Sn k*acc = fact-iter n ((k * Sn) * acc)
--                   ]
--                 ...= fact-iter n (k * (Sn * acc))
--                    = k * fact-iter n (Sn * acc)
--                    = k * fact-iter Sn acc
fact-commut-mult (suc n) k acc =
  begin
                                            fact-iter (suc n) (k * acc)
    =⟨⟩                                     fact-iter n (suc n * (k * acc))
    =⟨ ap (λ e → fact-iter n e) (left-ac-* (suc n) k acc) ⟩
                                            fact-iter n (k * (suc n * acc))
    =⟨ fact-commut-mult n k (suc n * acc) ⟩ k * fact-iter n (suc n * acc)
    =⟨⟩                                     k * fact-iter (suc n) acc
  ∎

fact-lemma : (n acc : ℕ) → fact-iter (suc n) acc ＝ suc n * fact-iter n acc
fact-lemma zero    acc = refl _
-- IH : fact-iter Sn acc ＝ Sn * fact-iter n acc
-- fact-iter (SSn) acc = fact-iter Sn (SSn * acc)
--                     = Sn * fact-iter n (SSn * acc)
--                     = Sn * (SSn * fact-iter n acc)
--                     = SSn * (Sn * fact-iter n acc)
--                     = SSn * fact-iter Sn acc
fact-lemma (suc n) acc =
  begin
                                          fact-iter (suc (suc n)) acc
    =⟨⟩                                   fact-iter (suc n) ((suc (suc n)) * acc)
    =⟨ fact-lemma n (suc (suc n) * acc) ⟩ suc n * fact-iter n (suc (suc n) * acc)
    =⟨ ap (λ e → suc n * e) (fact-commut-mult n (suc (suc n)) acc) ⟩
                                          suc n * (suc (suc n) * fact-iter n acc)
    =⟨ left-ac-* (suc n) (suc (suc n)) (fact-iter n acc) ⟩
                                          suc (suc n) * (suc n * fact-iter n acc)
    =⟨ ap (λ e → suc (suc n) * e) (sym＝ (fact-lemma n acc)) ⟩
                                          suc (suc n) * fact-iter (suc n) acc
  ∎

factorial-rec : (n : ℕ) → factorial (suc n) ＝ (suc n) * factorial n
factorial-rec zero    = refl _
factorial-rec (suc n) = fact-lemma (suc n) 1

{-
  fib TODO insert into demo
-}

-- *0* 1 1 *2* 3 5 *8* 13 21 *34* ...
fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc a)) = fib a + fib (suc a)

-- take any predicate P(n, m) including the least relation (n, fib n)
fib-principle : {P : ℕ → ℕ → Set}
              → (P 0 0) → (P 1 1)
              → (∀{n fn fm : ℕ} → (P n fn) → (P (suc n) fm)
                                → P (suc (suc n)) (fn + fm))
              → ∀ n → P n (fib n)
fib-principle {P} p0 p1 psuc = fib-principle'
  where
    fib-principle' : ∀ n → P n (fib n)
    fib-principle' 0 = p0
    fib-principle' 1 = p1
    fib-principle' (suc (suc n)) = psuc (fib-principle' n) (fib-principle' (suc n))

mutual
  data even : ℕ → Set where
    ev0 : even 0
    evS : (n : ℕ) → odd n → even (suc n)

  data odd : ℕ → Set where
    oddS : (n : ℕ) → even n → odd (suc n)

-- (n = 0 mod 3, odd fn) (n = 1 mod 3, odd fn) (n = 3 mod 3, even fn)
-- fib-triples→even : (n : ℕ) → triple n → even (fib n)

-- fib-even→triple : (n : ℕ) → even (fib n) → triple n
-- fib-even→triple zero    is-even = triple-0
-- fib-even→triple (suc a) is-even = ?

{-
  choice
-}

open import Agda.Primitive
open import hott

choice-theorem : (X : Set ℓ) (A : X → Set ℓ₁)
               → (R : (x : X) → A x → Set ℓ₂)
               → ((x : X) → Σ a ∶ A x , R x a)
               → Σ f ∶ Π A , ((x : X) → R x (f x))
choice-theorem X A R s = (λ x → pr₁ (s x)) , λ x → pr₂ (s x)
