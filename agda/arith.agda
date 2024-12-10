{-# OPTIONS --without-K --exact-split --safe #-}

{-
  number theory
-}

open import logic
open import types
open import path
open import op
open import hlevel

-- peano +
_+_ : ℕ → ℕ → ℕ
zero    + b = b
(suc a) + b = suc (a + b)
infix 7 _+_

_*_ : ℕ → ℕ → ℕ
zero    * b = 0
(suc a) * b = (a * b) + b
infix 8 _*_

suc-x≠0 : (x : ℕ) → suc x ≠ 0 -- peano axiom, note pattern lambda!
suc-x≠0 _ p = 𝟙≠𝟘 (ap (λ { 0 → 𝟘 ; (suc _) → 𝟙 }) p)

-- lambda style predecessor
pred' : ℕ → ℕ
pred' n = snd (pred'' n) where
          pred'' : ℕ → ℕ × ℕ
          pred'' zero = (zero , zero)
          pred'' (suc n) = (suc (fst (pred'' n)) , fst (pred'' n))

pred : ℕ → ℕ
pred zero    = 0
pred (suc n) = n

suc-cancel : {x y : ℕ} → suc x ＝ suc y → x ＝ y
suc-cancel = ap pred

ℕ-decidable-equality : ℕ has-decidable-equality
ℕ-decidable-equality zero    zero    = (inl (refl zero))
ℕ-decidable-equality zero    (suc b) = inr (≠-sym (suc-x≠0 b))
ℕ-decidable-equality (suc a) zero    = inr (suc-x≠0 a)
ℕ-decidable-equality (suc a) (suc b) = f (ℕ-decidable-equality a b)
  where
    f = ind＋ (λ _ → decidable (suc a ＝ suc b))
        (λ (p : a ＝ b) → inl (ap suc p))
        (λ (f : a ≠ b) → inr (f ∘ suc-cancel))

{-
  inequality
-}

_≤'_ : ℕ → ℕ → Set
n ≤' zero    = n ＝ 0
n ≤' (suc m) = (n ＝ suc m) ＋ n ≤' m

refl-≤' : (n : ℕ) → (n ≤' n)
refl-≤' zero = refl 0
refl-≤' (suc n) = inl (refl (suc n))

trans-≤' : (l m n : ℕ) → (l ≤' m) → (m ≤' n) → (l ≤' n)
trans-≤' n m    zero p (refl .0) = p
trans-≤' n zero (suc l) (refl .0) q = q
trans-≤' n (suc m) (suc l) (inl p) (inl q) = inl (p ∙ q)
trans-≤' n (suc m) (suc l) (inl p) (inr q) = inr (subst (λ x → x ≤' l) (sym＝ p) q)
trans-≤' n (suc m) (suc l) (inr p) (inl q) = inr (subst (λ x → n ≤' x)
                                                   (suc-cancel q) p)
trans-≤' n (suc m) (suc l) (inr p) (inr q) = inr (trans-≤' _ _ _ (inr p) q)

anti-≤' : (m n : ℕ) → (m ≤' n) → (n ≤' m) → (m ＝ n)
anti-≤' zero n p q = sym＝ q
anti-≤' (suc m) n p (inl q) = sym＝ q
anti-≤' (suc m) (suc n) (inl p) (inr q) = p
anti-≤' (suc m) (suc n) (inr p) (inr q) = ap suc (anti-≤' m n (l p) (l q))
  where
    l : {m n : ℕ} → suc n ≤' m → n ≤' m
    l {m} {n} p = trans-≤' n (suc n) m (inr (refl-≤' n)) p

-- cleaner def
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

refl-≤ : (n : ℕ) → (n ≤ n)
refl-≤ zero    = z≤n
refl-≤ (suc n) = s≤s (refl-≤ n)

trans-≤ : (l m n : ℕ) → (l ≤ m) → (m ≤ n) → (l ≤ n)
trans-≤ zero _ _ _ _ = z≤n
trans-≤ (suc l) (suc m) (suc n) (s≤s p) (s≤s q) = s≤s (trans-≤ l m n p q)

anti-≤ : (m n : ℕ) → (m ≤ n) → (n ≤ m) → (m ＝ n)
anti-≤ zero zero _ _ = refl zero
anti-≤ (suc m) (suc n) (s≤s p) (s≤s q) = ap suc (anti-≤ m n p q)

_≥_ : ℕ → ℕ → Set
x ≥ y = y ≤ x
infix 4 _≤_ _≥_

-- strict inequality
_<_ _>_ : ℕ → ℕ → Set
x < y = suc x ≤ y
x > y = suc y ≥ x
infix 4 _<_ _>_

{-
  addition
-}

assoc-+ : (assoc _+_)
assoc-+ zero    y z = refl (y + z)
assoc-+ (suc x) y z = ap suc (assoc-+ x y z)

-- commutativity of addition
idr-+ : (n : ℕ) → (n + 0) ＝ n
idr-+ zero = refl 0
idr-+ (suc n) =
  begin                   suc n  + 0
    =⟨⟩                   suc (n + 0)
    =⟨ ap suc (idr-+ n) ⟩ suc n        -- induction hypothesis
  ∎

commutes-sucr-+ : (m n : ℕ) → suc (m + n) ＝ (m + suc n)
commutes-sucr-+ zero n =
  begin suc (0 + n)
    =⟨⟩ suc n
    =⟨⟩ 0 + suc n
  ∎
commutes-sucr-+ (suc m) n =
  begin                               suc (suc m  + n)
    =⟨⟩                               suc (suc (m + n))
    =⟨ ap suc (commutes-sucr-+ m n) ⟩ suc (m + suc n)
    =⟨⟩                               suc m  + suc n
  ∎

commutes-+ : commut _+_
commutes-+ zero n =
  begin                 0 + n
    =⟨⟩                 n
    =⟨ sym＝ (idr-+ n) ⟩ n + 0
  ∎
commutes-+ (suc m) n =
  begin                          suc m  + n
    =⟨⟩                          suc (m + n)
    =⟨ ap suc (commutes-+ m n) ⟩ suc (n + m)
    =⟨ commutes-sucr-+ n m ⟩     n + suc m
  ∎

left-ac-+ = left-ac _+_ assoc-+ commutes-+
right-ac-+ = right-ac _+_ assoc-+ commutes-+

-- cancellation
cancel-+ : (x y z : ℕ) → (x + y ＝ x + z) → (y ＝ z)
cancel-+ zero    y z p = p
cancel-+ (suc x) y z p = (cancel-+ x y z (ap pred p))

n+1＝suc : (n : ℕ) → n + 1 ＝ suc n
n+1＝suc n = commutes-+ n 1

{-
  subtraction TODO
-}

-- signed type needed
data ℤ : Set where
  pos : (n : ℕ) → ℤ
  neg : (n : ℕ) → ℤ
{-# BUILTIN INTEGER ℤ #-}
{-# BUILTIN INTEGERPOS pos #-}
{-# BUILTIN INTEGERNEGSUC neg #-}

{-
  multiplication
-}
-- _*_ : ℕ → ℕ → ℕ
-- zero    * b = 0
-- (suc a) * b = (a * b) + b

idr-* : (n : ℕ) → n * 1 ＝ n
idr-* zero = refl _
idr-* (suc n) = ap (λ e → e + 1) (idr-* n) ∙ n+1＝suc n

ldistrib-*-+ : (a b c : ℕ) → a * (b + c) ＝ a * b + a * c
ldistrib-*-+ zero b c = refl _
ldistrib-*-+ (suc a) b c =
  begin                                                    suc a * (b + c)
    =⟨⟩                                                    a * (b + c) + (b + c)
    =⟨ ap (λ e → e + (b + c)) (ldistrib-*-+ a b c) ⟩       (a * b + a * c) + (b + c)
    =⟨ right-ac-+ (a * b) (a * c) (b + c) ⟩                (a * b + (b + c)) + a * c
    =⟨ ap (λ e → e + a * c) (sym＝ (assoc-+ (a * b) b c)) ⟩ (suc a * b + c) + a * c
    =⟨ assoc-+ (suc a * b) c (a * c) ⟩                     suc a * b + (c + a * c)
    =⟨ ap (λ e → suc a * b + e) (commutes-+ c (a * c)) ⟩   suc a * b + suc a * c
  ∎

rdistrib-*-+ : (a b c : ℕ) → (a + b) * c ＝ a * c + b * c
rdistrib-*-+ zero b c = refl _
rdistrib-*-+ (suc a) b c =
  begin                                        (suc a + b) * c
    =⟨⟩                                        suc (a + b) * c
    =⟨⟩                                        (a + b) * c + c
    =⟨ ap (λ e → e + c) (rdistrib-*-+ a b c) ⟩ (a * c + b * c) + c
    =⟨ right-ac-+ (a * c) (b * c) c ⟩          (a * c + c) + b * c
    =⟨⟩                                        suc a * c + b * c
  ∎

zero-* : (n : ℕ) → n * 0 ＝ 0
zero-* zero = refl _
zero-* (suc n) = idr-+ (n * 0) ∙ zero-* n

commutes-* : commut _*_
commutes-* zero b = sym＝ (zero-* b)
commutes-* (suc a) b =
  begin                                        suc a * b
    =⟨⟩                                        a * b + b
    =⟨ ap (λ e → e + b) (commutes-* a b) ⟩     b * a + b
    =⟨ ap (λ e → b * a + e) (sym＝ (idr-* b)) ⟩ b * a + b * 1
    =⟨ sym＝ (ldistrib-*-+ b a 1) ⟩             b * (a + 1)
    =⟨ ap (λ e → b * e) (n+1＝suc a) ⟩          b * suc a
  ∎

assoc-* : assoc _*_
assoc-* zero    y z = refl _
assoc-* (suc x) y z =
  begin                                         (suc x * y) * z
    =⟨⟩                                         ((x * y) + y) * z
    =⟨ rdistrib-*-+ (x * y) y z ⟩               (x * y) * z + y * z
    =⟨ ap (λ e → e + (y * z)) (assoc-* x y z) ⟩ x * (y * z) + y * z
    =⟨⟩                                         suc x * (y * z)
  ∎

left-ac-* = left-ac _*_ assoc-* commutes-*
right-ac-* = right-ac _*_ assoc-* commutes-*

{-
  multiples
-}

data Multiple : ℕ → ℕ → Set where
  div-zero : (k : ℕ) → Multiple k 0
  div-suck : {n k : ℕ} → Multiple k n → Multiple k (n + k) -- oops!

test-multiple : Multiple 3 6
test-multiple = div-suck (div-suck (div-zero 3))

div-coe : {a b k : ℕ} → Multiple k (a + b) → Multiple k (b + a)
div-coe {a} {b} {k} m = subst (λ n → Multiple k n) (commutes-+ a b) m

div-four→div-two : {n : ℕ} → Multiple 4 n → Multiple 2 n
div-four→div-two (div-zero .4) = div-zero 2
div-four→div-two (div-suck {k} {4} p) =
  (div-coe {4} {k}
   (div-coe {2 + k} {2}
    (div-suck {2 + k} {2}
     (div-coe {k} {2}
      (div-suck {k} {2} (div-four→div-two p))))))
