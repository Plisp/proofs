{-# OPTIONS --without-K --exact-split --safe #-}

{-
  univalent math, hott chapter 3
-}

open import Agda.Primitive
open import logic
open import types
open import path

{-
  -1-type (contractible)
-}

is-center : (X : Set ℓ) → X → Set ℓ
is-center X c = (x : X) → c ＝ x

is-contr : Set ℓ → Set ℓ
is-contr X = Σ c ∶ X , is-center X c

𝟙-is-singleton : is-contr 𝟙
𝟙-is-singleton = ⋆ , ind⊤ (λ x → ⋆ ＝ x) (refl ⋆)

center : (X : Set ℓ) → is-contr X → X
center X (c , p) = c

centrality : (X : Set ℓ) (i : is-contr X) → (x : X) → center X i ＝ x
centrality X (c , p) = p

singleton-type : {X : Set ℓ} → X → Set ℓ
singleton-type {ℓ} {X} x = Σ c ∶ X , c ＝ x

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

-- (subtype) singletons but maybe not inhabited
is-subsingleton : Set ℓ → Set ℓ
is-subsingleton X = (x y : X) → x ＝ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = ind⊥ (λ x → (x ＝ y)) x

is-prop = is-subsingleton

singletons-are-subsingletons : (X : Set ℓ) → is-contr X → is-subsingleton X
singletons-are-subsingletons X (c , p) x y = sym＝ (p x) ∙ p y

pointed-subsingleton→singleton : (X : Set ℓ) → X
                               → is-subsingleton X → is-contr X
pointed-subsingleton→singleton X x s = (x , s x)

{-
  n-types/groupoids ↔ hlevel n+2
-}

0-type : Set ℓ → Set ℓ
0-type X = (x y : X) → is-subsingleton (x ＝ y)

is-set = 0-type

1-type : Set ℓ → Set ℓ
1-type X = {x y : X} (p q : x ＝ y) → is-subsingleton (p ＝ q)

_is-of-hlevel_ : Set ℓ → ℕ → Set ℓ
X is-of-hlevel zero    = is-contr X
X is-of-hlevel (suc n) = (x x' : X) → ((x ＝ x') is-of-hlevel n)

-- if all points connected, then all 2-paths are trivial
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
    -- p ∙ q ＝ r  ≃  q ＝ sym＝ p ∙ r, or just make holes and C-c C-a
    lemma : {x y : X} (p : x ＝ y) → p ＝ sym＝ (ss x x) ∙ (ss x y)
    lemma {x} {y} p = p＝refl∙p p ∙ ap (λ e → e ∙ p) (sym＝ (iv∙p＝refl (ss x x)))
                    ∙ assoc∙ _ _ p ∙ ap (λ e → sym＝ (ss x x) ∙ e) (lemma0 p)

    proof : (x y : X) (p q : x ＝ y) → p ＝ q
    proof x y p q = lemma p ∙ sym＝ (lemma q)

-- the levels are upper closed
hlevel-suc : (X : Set ℓ) (n : ℕ)
           → X is-of-hlevel n → X is-of-hlevel (suc n)
hlevel-suc X zero    = λ h → λ x y →
                         let k = singletons-are-subsingletons X h in
                             (k x y , subsingleton→set X k x y (k x y))
-- lift H (suc n) X using X = (x＝y) in ind (H n T -> H (suc n) T)
hlevel-suc X (suc n) = λ h → λ x y → hlevel-suc (x ＝ y) n (h x y)

-- equalities are of a hlevel that's one less
hlevel-eq : {X : Set ℓ} {n : ℕ}
          → X is-of-hlevel (suc n)
          → (x y : X) → (x ＝ y) is-of-hlevel n
hlevel-eq {ℓ}{X} {n} p x y = p x y

𝟘-is-set : is-set 𝟘
𝟘-is-set = subsingleton→set 𝟘 𝟘-is-subsingleton

{-
  decidable
-}

decidable : Set ℓ → Set ℓ
decidable A = A ＋ ¬ A

has-decidable-equality : Set ℓ → Set ℓ
has-decidable-equality A = (x y : A) → decidable (x ＝ y)

is-empty : Set ℓ → Set ℓ
is-empty X = ¬ X

LEM LEM' : ∀ ℓ → Set (lsuc ℓ)
LEM ℓ = (X : Set ℓ) → is-prop X → decidable X
LEM' ℓ = (X : Set ℓ) → is-subsingleton X → is-contr X ＋ is-empty X
