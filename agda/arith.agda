{-# OPTIONS --without-K --exact-split #-}
open import logic
open import types
open import eq

-- lambda style predecessor
pred : ℕ → ℕ
pred n = snd (pred' n) where
         pred' : ℕ → ℕ × ℕ
         pred' zero = (zero , zero)
         pred' (suc n) = (suc (fst (pred' n)) , fst (pred' n))

-- TODO
ℕ-decidable-equality : has-decidable-equality ℕ
ℕ-decidable-equality =
  λ a b → ℕ-ind (λ a → ((a ＝ b) ＋ (a ≠ b))) (f b) {!!} a
    where
      f = ℕ-ind (λ (b : ℕ) → (0 ＝ b) ＋ (0 ≠ b))
                (inl (refl 0))
                (λ (a : ℕ) _ → inr ((suc-neq-zero a) ≠⁻¹))

-- commutativity of addition
add-commutes0 : (n : ℕ) → (n + 0) ＝ n
add-commutes0 0 =
  Proof
    0 + 0 =⟨⟩ 0
  ∎
add-commutes0 (suc n) =
  Proof
                                  suc n  + 0
    =⟨⟩                           suc (n + 0)
    =⟨ ap suc (add-commutes0 n) ⟩ suc n        -- induction hypothesis
  ∎

add-commutes-sucr : (m n : ℕ) → suc (m + n) ＝ (m + suc n)
add-commutes-sucr 0 n =
  Proof
        suc (0 + n)
    =⟨⟩ suc n
    =⟨⟩ 0 + suc n
  ∎
add-commutes-sucr (suc m) n =
  Proof
                                        suc (suc m  + n)
    =⟨⟩                                 suc (suc (m + n))
    =⟨ ap suc (add-commutes-sucr m n) ⟩ suc (m + suc n)
    =⟨⟩                                 suc m  + suc n
  ∎

add-commutes : (m n : ℕ) → (m + n) ＝ (n + m)
add-commutes 0 n =
  Proof
                              0 + n
    =⟨⟩                       n
    =⟨ (add-commutes0 n) ⁻¹ ⟩ n + 0
  ∎
add-commutes (suc m) n =
  Proof
                                   suc m  + n
    =⟨⟩                            suc (m + n)
    =⟨ ap suc (add-commutes m n) ⟩ suc (n + m)
    =⟨ add-commutes-sucr n m ⟩     n + suc m
  ∎

-- multiples
data Multiple : ℕ → ℕ → Set where
  div-zero : (k : ℕ) → Multiple k 0
  div-suck : {n k : ℕ} → Multiple k n → Multiple k (n + k) -- oops!

test-multiple : Multiple 3 6
test-multiple = div-suck (div-suck (div-zero 3))

div-coe : {a b k : ℕ} → Multiple k (a + b) → Multiple k (b + a)
div-coe {a} {b} {k} m = ȷ (Multiple k) (add-commutes a b) m

div-four→div-two : {n : ℕ} → Multiple 4 n → Multiple 2 n
div-four→div-two (div-zero .4) = div-zero 2
div-four→div-two (div-suck {k} {4} p) =
  (div-coe {4} {k}
   (div-coe {2 + k} {2}
    (div-suck {2 + k} {2}
     (div-coe {k} {2}
      (div-suck {k} {2} (div-four→div-two p))))))
