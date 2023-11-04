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
  fib
-}

-- *0* 1 1 *2* 3 5 *8* 13 21 *34* ...
fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc a)) = fib a + fib (suc a)

mutual
  data even : ℕ → Set where
    ev0 : even 0
    evS : {n : ℕ} → odd n → even (suc n)

  data odd : ℕ → Set where
    oddS : {n : ℕ} → even n → odd (suc n)

  data tripl : ℕ → Set where
    t0 : tripl 0
    t0S : {n : ℕ} → trip2 n → tripl (suc n)

  data trip1 : ℕ → Set where
    t1S : {n : ℕ} → tripl n → trip1 (suc n)

  data trip2 : ℕ → Set where
    t2S : {n : ℕ} → trip1 n → trip2 (suc n)

-- even theorems
evn-dec : {n : ℕ} → even (suc n) → odd n
evn-dec {0} (evS ()) -- 1 isn't even
evn-dec {suc n} (evS x) = x

odd-dec : {n : ℕ} → odd (suc n) → even n
odd-dec {0} (oddS ev0) = ev0
odd-dec {suc n} (oddS x) = x

odd+odd=even : {a b : ℕ} → odd a → odd b → even (a + b)
odd+odd=even {0} {b} ()
odd+odd=even {1} {b} oa ob = evS ob
odd+odd=even {suc (suc a)} {b} oSSa ob = evS (oddS (odd+odd=even oa ob))
  where
  oa : odd a
  oa = evn-dec (odd-dec oSSa)

odd+even=odd : {a b : ℕ} → odd a → even b → odd (a + b)
odd+even=odd {0} {b} ()
odd+even=odd {1} {b} oa eb = oddS eb
odd+even=odd {suc (suc a)} {b} oSSa eb = oddS (evS
                                         (odd+even=odd (evn-dec (odd-dec oSSa)) eb))

even+odd=odd : {a b : ℕ} → even a → odd b → odd (a + b)
even+odd=odd {a} {b} ea ob = -- ooh!
  transport (λ x → odd x) (commutes-+ b a) (odd+even=odd {b} {a} ob ea)

-- trip theorems
tripl-dec : {n : ℕ} → tripl (suc n) → trip2 n
tripl-dec {0} (t0S ())
tripl-dec {1} (t0S (t2S ()))
tripl-dec {2} _ = t2S (t1S t0)
tripl-dec {suc (suc (suc n))} (t0S x) = x

trip1-dec : {n : ℕ} → trip1 (suc n) → tripl n
trip1-dec {0} p = t0
trip1-dec {1} (t1S (t0S ()))
trip1-dec {2} (t1S (t0S (t2S ())))
trip1-dec {suc (suc (suc n))} (t1S x) = x

trip2-dec : {n : ℕ} → trip2 (suc n) → trip1 n
trip2-dec {0} (t2S ())
trip2-dec {1} (t2S (t1S t0)) = t1S t0
trip2-dec {2} (t2S (t1S (t0S ())))
trip2-dec {suc (suc (suc n))} (t2S x) = x

mutual
  tripl-fib-even : (n : ℕ) → tripl n → even (fib n)
  tripl-fib-even 0 _ = ev0
  tripl-fib-even 1 (t0S ())
  tripl-fib-even (suc (suc n)) pSSn =
    odd+odd=even (trip1-fib-odd n x) (trip2-fib-odd (suc n) y)
    where
    x : trip1 n
    x = trip2-dec (tripl-dec pSSn)
    y : trip2 (suc n)
    y = tripl-dec pSSn

  trip1-fib-odd : (n : ℕ) → trip1 n → odd (fib n)
  trip1-fib-odd 0 ()
  trip1-fib-odd 1 _ = oddS ev0
  trip1-fib-odd (suc (suc n)) pSSn =
    odd+even=odd (trip2-fib-odd n (tripl-dec (trip1-dec pSSn)))
                 (tripl-fib-even (suc n) (trip1-dec pSSn))

  trip2-fib-odd : (n : ℕ) → trip2 n → odd (fib n)
  trip2-fib-odd 0 ()
  trip2-fib-odd 1 _ = oddS ev0 -- fib 1 = 1
  trip2-fib-odd (suc (suc n)) pSSn =
    even+odd=odd (tripl-fib-even n (trip1-dec (trip2-dec pSSn)))
                 (trip1-fib-odd (suc n) (trip2-dec pSSn))

-- deriving the contradiction

all-trip : ∀ n → tripl n ＋ trip1 n ＋ trip2 n
all-trip 0 = inl t0
all-trip (suc n) with (all-trip n)
...              | inl r0 = inr (inl (t1S r0))
...              | inr (inl r1) = inr (inr (t2S r1))
...              | inr (inr r2) = inl (t0S r2)

not-tripl-odd : ∀ n → ¬ (tripl n) → odd (fib n)
not-tripl-odd n = trip12-fib-odd ∘ (not-tripl-trip12 n)
  where
  trip12-fib-odd : ∀ {n} → trip1 n ＋ trip2 n → odd (fib n)
  trip12-fib-odd {n} (inl t1) = trip1-fib-odd n t1
  trip12-fib-odd {n} (inr t2) = trip2-fib-odd n t2

  not-tripl-trip12 : ∀ n → ¬ (tripl n) → trip1 n ＋ trip2 n
  not-tripl-trip12 n p with (all-trip n)
  ...                   | inl t = rec⊥ _ (p t)
  ...                   | inr x = x

odd-not-even : ∀ {n} → odd n → ¬ (even n)
odd-not-even {0} ()
odd-not-even {suc n} (oddS en) (evS on) = odd-not-even on en

contrℕ : {A B : ℕ → Set}
       → (∀ n → B n ＋ ¬ (B n))
       → (∀ n → ¬ (B n) → ¬ (A n))
       → (∀ n → (A n → B n))
contrℕ {A} {B} lemb contrab n an =
  rec＋ (B n) (λ bn → bn) (λ nbn → rec⊥ (B n) (contrab n nbn an)) (lemb n)

Lem = (P : ℕ → Set) → ∀ n → (P n) ＋ ¬ (P n)

even-triples-only0 : Lem → ∀ n → even (fib n) → tripl n
even-triples-only0 lem = contrℕ (lem tripl) (λ n → odd-not-even ∘ not-tripl-odd n)

{-
  constructive proof
-}

contravariance : {A B : Set} → (A → B) → (¬ B → ¬ A)
contravariance ab nb = nb ∘ ab

contradiction : {A B : Set} → (B ＋ ¬ B) → (¬ B → ¬ A) → (A → B)
contradiction (inl b) nba a = b
contradiction {A}{B} (inr nb) nb→na a = rec⊥ B ((nb→na nb) a)

mutual
  trip1-not-trip : ∀ {n} → trip1 n → ¬ (tripl n)
  trip1-not-trip {0} ()
  trip1-not-trip {suc n} (t1S r0) (t0S r2) = trip2-not-trip r2 r0

  trip2-not-trip : ∀ {n} → trip2 n → ¬ (tripl n)
  trip2-not-trip {0} ()
  trip2-not-trip {1} (t2S ())
  trip2-not-trip {suc (suc n)} (t2S (t1S r0)) (t0S (t2S r1)) = trip1-not-trip r1 r0

tripl-decidable : ∀ n → tripl n ＋ ¬ (tripl n)
tripl-decidable n with (all-trip n)
...                | inl r0 = inl r0
...                | inr (inl r1) = inr (trip1-not-trip r1)
...                | inr (inr r2) = inr (trip2-not-trip r2)

even-triples-only : ∀ n → even (fib n) → tripl n
even-triples-only = contrℕ tripl-decidable (λ n → odd-not-even ∘ not-tripl-odd n)

{-
  fib part 2
-}

--take any predicate P(n, m) including the least relation (n, fib n)
fib-principle : (P : ℕ → ℕ → Set)
              → (P 0 0) → (P 1 1)
              → (∀{n fn fm} → P n fn → P (suc n) fm → P (suc (suc n)) (fn + fm))
              → ∀ n → P n (fib n)
fib-principle P p0 p1 psuc = fib-principle'
  where
  fib-principle' : ∀ n → P n (fib n)
  fib-principle' 0 = p0
  fib-principle' 1 = p1
  fib-principle' (suc (suc n)) = psuc (fib-principle' n) (fib-principle' (suc n))

-- isabelle version
fib-principle2 : (Q : ℕ → Set)
               → (Q 0) → (Q 1)
               → (∀{n : ℕ} → (Q n) → (Q (suc n)) → (Q (suc (suc n))))
               → ∀ n → Q n
fib-principle2 Q q0 q1 qsuc = fib-principle (λ a fa → Q a) q0 q1 qsuc

{-
  choice
-}

open import Agda.Primitive
open import hott

choice-theorem : (X : Set ℓ) (A : X → Set ℓ₁) -- for every indexed family A
               → (R : (x : X) → A x → Set ℓ₂)
               → ((x : X) → Σ a ∶ A x , R x a) -- already contains the witness
               → Σ f ∶ Π A , ((x : X) → R x (f x)) -- choose one for each index
choice-theorem X A R s = (λ x → pr₁ (s x)) , (λ x → pr₂ (s x))
