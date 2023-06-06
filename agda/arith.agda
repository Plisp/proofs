{-# OPTIONS --without-K --exact-split --safe #-}

{-
  number theory
-}

open import logic
open import types
open import eq
open import op

-- lambda style predecessor
pred' : ℕ → ℕ
pred' n = snd (pred'' n) where
          pred'' : ℕ → ℕ × ℕ
          pred'' zero = (zero , zero)
          pred'' (suc n) = (suc (fst (pred'' n)) , fst (pred'' n))

pred : ℕ → ℕ
pred 0       = 0
pred (suc n) = n

cancel-suc : {x y : ℕ} → suc x ＝ suc y → x ＝ y
cancel-suc = ap pred

ℕ-decidable-equality : has-decidable-equality ℕ
ℕ-decidable-equality 0       0       = (inl (refl 0))
ℕ-decidable-equality 0       (suc b) = inr (≠-sym (suc-neq-zero b))
ℕ-decidable-equality (suc a) 0       = inr (suc-neq-zero a)
ℕ-decidable-equality (suc a) (suc b) = f (ℕ-decidable-equality a b)
  where
    f = ＋-ind (λ _ → decidable (suc a ＝ suc b))
        (λ (p : a ＝ b) → inl (ap suc p))
        (λ (f : a ≠ b) → inr (f ∘ cancel-suc))

{-
  inequality TODO prove this is equivalent to other one
-}

_≼_ : ℕ → ℕ → Set
x ≼ y = Σ z ꞉ ℕ , (x + z) ＝ y

infix 4 _≼_

-- partial order of ≤
-- 0     ≤ y     = 𝟙
-- suc x ≤ 0     = 𝟘
-- suc x ≤ suc y = x ≤ y

≤-refl : (n : ℕ) → (n ≤ n)
≤-refl 0       = ⋆
≤-refl (suc n) = ≤-refl n

≤-trans : (l m n : ℕ) → (l ≤ m) → (m ≤ n) → (l ≤ n)
≤-trans 0 l n _ _ = ⋆
≤-trans (suc l) 0       0       p q = p
≤-trans (suc l) 0       (suc n) p q = ⊥-rec (suc l ≤ suc n) p
≤-trans (suc l) (suc m) 0       p q = q
≤-trans (suc l) (suc m) (suc n) p q = ≤-trans l m n p q

≤-anti : (m n : ℕ) → m ≤ n → n ≤ m → m ＝ n
≤-anti 0       0       p q = refl 0
≤-anti 0       (suc n) p q = ⊥-rec (0 ＝ suc n) q
≤-anti (suc m) 0       p q = ⊥-rec (suc m ＝ 0) p
≤-anti (suc m) (suc n) p q = ap suc (≤-anti m n p q)

-- strict inequality
_<_ _>_ : ℕ → ℕ → Set
x < y = suc x ≤ y
x > y = suc y ≥ x
infix 4 _<_ _>_

{-
  addition
-}

+-assoc : (op-assoc _+_)
+-assoc 0       y z = refl (y + z)
+-assoc (suc x) y z = ap suc (+-assoc x y z)

-- commutativity of addition
add-commutes0 : (n : ℕ) → (n + 0) ＝ n
add-commutes0 0 = refl 0
add-commutes0 (suc n) =
  begin                           suc n  + 0
    =⟨⟩                           suc (n + 0)
    =⟨ ap suc (add-commutes0 n) ⟩ suc n        -- induction hypothesis
  ∎

add-commutes-sucr : (m n : ℕ) → suc (m + n) ＝ (m + suc n)
add-commutes-sucr 0 n =
  begin suc (0 + n)
    =⟨⟩ suc n
    =⟨⟩ 0 + suc n
  ∎
add-commutes-sucr (suc m) n =
  begin                                 suc (suc m  + n)
    =⟨⟩                                 suc (suc (m + n))
    =⟨ ap suc (add-commutes-sucr m n) ⟩ suc (m + suc n)
    =⟨⟩                                 suc m  + suc n
  ∎

add-commutes : (op-commut _+_)
add-commutes 0 n =
  begin                        0 + n
    =⟨⟩                        n
    =⟨ sym (add-commutes0 n) ⟩ n + 0
  ∎
add-commutes (suc m) n =
  begin                            suc m  + n
    =⟨⟩                            suc (m + n)
    =⟨ ap suc (add-commutes m n) ⟩ suc (n + m)
    =⟨ add-commutes-sucr n m ⟩     n + suc m
  ∎

-- cancellation
+-cancel : (x y z : ℕ) → (x + y ＝ x + z) → (y ＝ z)
+-cancel 0       y z p = p
+-cancel (suc x) y z p = (+-cancel x y z (ap pred p))

{-
  subtraction TODO prove inverse theorems
-}

-- signed type needed
data ℤ : Set where
  pos : (n : ℕ) → ℤ
  neg : (n : ℕ) → ℤ
{-# BUILTIN INTEGER ℤ #-}
{-# BUILTIN INTEGERPOS pos #-}
{-# BUILTIN INTEGERNEGSUC neg #-}

{-
  multiples
-}

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
