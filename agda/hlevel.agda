{-# OPTIONS --without-K --exact-split --safe #-}

{-
  univalent math, hott chapter 3
-}

open import Agda.Primitive
open import logic
open import types
open import path

{-
  -2-type (contractible)
-}

is-center : {X : Set ℓ} → X → Set ℓ
is-center {X = X} c = (x : X) → c ＝ x

is-contr : Set ℓ → Set ℓ
is-contr X = Σ c ∶ X , is-center c

center : (X : Set ℓ) → is-contr X → X
center X (c , p) = c

centrality : {X : Set ℓ} (i : is-contr X) → (x : X) → center X i ＝ x
centrality (c , p) = p

singleton-type : {X : Set ℓ} → X → Set ℓ
singleton-type {X = X} x = Σ c ∶ X , c ＝ x

singleton-type-center : {X : Set ℓ} (x : X) → singleton-type x
singleton-type-center x = (x , refl x)

-- refl makes this trivial, since we have any (x, x ＝ y) is simply (x, refl x)
singleton-type-centered : {X : Set ℓ} (x : X) (σ : singleton-type x)
                        → singleton-type-center x ＝ σ
singleton-type-centered x (x , refl x) = refl (x , refl x)

 -- is-contr (Σ y , y ＝ x) is of the form Σ c , (x , refl x) ＝ c
singleton-types-are-singletons : (X : Set ℓ) (x : X)
                               → is-contr (singleton-type x)
singleton-types-are-singletons X x
  = singleton-type-center x , singleton-type-centered x

{-
  -1-type (singletons but maybe not inhabited)
-}

is-subsingleton : Set ℓ → Set ℓ
is-subsingleton X = (x y : X) → x ＝ y

is-prop = is-subsingleton

singletons-are-subsingletons : (X : Set ℓ) → is-contr X → is-subsingleton X
singletons-are-subsingletons X (c , p) x y = sym＝ (p x) ∙ p y

pointed-subsingleton→singleton : (X : Set ℓ) → X → is-subsingleton X → is-contr X
pointed-subsingleton→singleton X x s = (x , s x)

{-
  0-type (sets/discrete)
-}

0-type : Set ℓ → Set ℓ
0-type X = (x y : X) → is-subsingleton (x ＝ y)
is-set = 0-type

-- any continuously* connected space has a trivial loop space
subsingleton→set : (X : Set ℓ) → is-subsingleton X → is-set X
subsingleton→set X ss = proof
  where
    lemma0 : {x y : X} (p : x ＝ y) → (ss x x) ∙ p ＝ (ss x y)
    lemma0 {x} {y} p = sym＝ (transport-startpoint p (ss x x)) ∙ apd (λ - → ss x -) p
    -- x＝x ∙ p ＝ (transp (λ - → x ＝ -) p x＝x)  ∙   (transp (λ - → x ＝ -) p x＝x) ＝ x＝y
    --
    -- (ss x -) is a family allowing (continuous) lifting p to x＝x -> x＝y, by ∙
    -- applying ∙ is homotopic to a transport of that endpoint
    --
    -- any path factors through the subsingleton proof
    -- x -p→ y
    --  \    ↑
    ---  ↓  /
    --    x
    -- p ∙ q ＝ r   ＝   q ＝ sym＝ p ∙ r, or just make holes and C-c C-a
    lemma : {x y : X} (p : x ＝ y) → p ＝ sym＝ (ss x x) ∙ (ss x y)
    lemma {x} {y} p = p＝refl∙p p ∙ ap (λ e → e ∙ p) (sym＝ (iv∙p＝refl (ss x x)))
                    ∙ assoc∙ _ _ p ∙ ap (λ e → sym＝ (ss x x) ∙ e) (lemma0 p)

    proof : (x y : X) (p q : x ＝ y) → p ＝ q
    proof x y p q = lemma p ∙ sym＝ (lemma q)

{-
  hlevel n+2 ↔ n-types
-}

_is-of-hlevel_ : Set ℓ → ℕ → Set ℓ
X is-of-hlevel zero    = is-contr X
X is-of-hlevel (suc n) = (x x' : X) → ((x ＝ x') is-of-hlevel n)

hlevel1-subsingleton : {X : Set ℓ} → X is-of-hlevel 1 → is-subsingleton X
hlevel1-subsingleton p x y = center _ (p x y)

-- if all points connected, then all 2-paths are trivial
subsingleton-hlevel1 : {X : Set ℓ} → is-subsingleton X → X is-of-hlevel 1
subsingleton-hlevel1 ss x y = ss x y , λ p → subsingleton→set _ ss x y _ _

-- the levels are upper closed
hlevel-suc : (X : Set ℓ) (n : ℕ) → (X is-of-hlevel n) → X is-of-hlevel (suc n)
hlevel-suc X zero    = λ h → λ x y →
                         let k = singletons-are-subsingletons X h in
                             (k x y , subsingleton→set X k x y (k x y))
-- lift H (suc n) X using X = (x＝y) in ind (H n T -> H (suc n) T)
hlevel-suc X (suc n) = λ h → λ x y → hlevel-suc (x ＝ y) n (h x y)

-- equalities are of a hlevel that's one less
hlevel-eq : {X : Set ℓ} {n : ℕ}
          → X is-of-hlevel (suc n)
          → (x y : X) → (x ＝ y) is-of-hlevel n
hlevel-eq {X = X} {n} p x y = p x y

{-
  decidable
-}

decidable : Set ℓ → Set ℓ
decidable A = A ＋ ¬ A

_has-decidable-equality : Set ℓ → Set ℓ
A has-decidable-equality = (x y : A) → decidable (x ＝ y)

is-empty : Set ℓ → Set ℓ
is-empty X = ¬ X

lem lem' : ∀ ℓ → Set (lsuc ℓ)
lem ℓ = (X : Set ℓ) → is-prop X → decidable X
lem' ℓ = (X : Set ℓ) → is-subsingleton X → is-contr X ＋ is-empty X
