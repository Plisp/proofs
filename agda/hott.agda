{-# OPTIONS --without-K --exact-split --safe #-}


{-
  univalent math, hott chapter 3
-}

open import Agda.Primitive
open import logic
open import types
open import eq

{-
  -1-type
-}

centerp : (X : Set ℓ) → X → Set ℓ
centerp X c = (x : X) → c ＝ x

singletonp : Set ℓ → Set ℓ
singletonp X = Σ c ∶ X , centerp X c

𝟙-is-singleton : singletonp 𝟙
𝟙-is-singleton = ⋆ , ind⊤ (λ x → ⋆ ＝ x) (refl ⋆)

center : (X : Set ℓ) → singletonp X → X
center X (c , p) = c

is-center : (X : Set ℓ) (i : singletonp X) → (x : X) → center X i ＝ x
is-center X (c , p) = p

-- (subtype) singletons but maybe not inhabited
subsingletonp : Set ℓ → Set ℓ
subsingletonp X = (x y : X) → x ＝ y

𝟘-is-subsingleton : subsingletonp 𝟘
𝟘-is-subsingleton x y = ind⊥ (λ x → (x ＝ y)) x

is-prop = subsingletonp

singleton→subsingleton : (X : Set ℓ) → singletonp X → subsingletonp X
singleton→subsingleton X (c , p) x y = sym＝ (p x) ∙ p y

pointed-subsingleton→singleton : (X : Set ℓ) → X → subsingletonp X → singletonp X
pointed-subsingleton→singleton X x s = (x , s x)

{-
  n-types
-}

0-typep : Set ℓ → Set ℓ
0-typep X = (x y : X) → subsingletonp (x ＝ y)

setp = 0-typep

1-typep : Set ℓ → Set ℓ
1-typep X = {x y : X} (p q : x ＝ y) → subsingletonp (p ＝ q)

_is-of-hlevel_ : Set ℓ → ℕ → Set ℓ
X is-of-hlevel 0       = singletonp X
X is-of-hlevel (suc n) = (x x' : X) → ((x ＝ x') is-of-hlevel n)

{-
  the levels are upper closed
-}

subsingleton→set : (X : Set ℓ) → subsingletonp X → setp X
subsingleton→set X ss = proof
  where
    g : {x : X} (y : X) → x ＝ y
    g {x} y = ss x y

    lemma : {x y y' : X} (r : y ＝ y') → (g y) ∙ r ＝ g y'
    lemma {x}{y} r = sym＝ (transportpq＝q∙p r (g y)) ∙ apd (g {x}) r

    proof : (x y : X) (p q : x ＝ y) → p ＝ q
    proof x y p q = lcancel∙ (g {x} x) p q (lemma p ∙ sym＝ (lemma q))

hlevel-suc : (X : Set ℓ) (n : ℕ)
           → X is-of-hlevel n → X is-of-hlevel (suc n)
hlevel-suc X 0       = λ h x y →
                         let k = singleton→subsingleton X h in
                             (k x y , subsingleton→set X k x y (k x y))
hlevel-suc X (suc n) = λ h x y → hlevel-suc (x ＝ y) n (h x y)

1-type-eqs-form-set : {X : Set ℓ} {x y : X} → 1-typep X → 0-typep (x ＝ y)
1-type-eqs-form-set {ℓ}{X} {x}{y} 1p = λ x y → 1p x y

𝟘-is-set : setp 𝟘
𝟘-is-set = subsingleton→set 𝟘 𝟘-is-subsingleton

{-
  decidable
-}

decidable : Set ℓ → Set ℓ
decidable A = A ＋ ¬ A

has-decidable-equality : Set ℓ → Set ℓ
has-decidable-equality A = (x y : A) → decidable (x ＝ y)

emptyp : Set ℓ → Set ℓ
emptyp X = ¬ X

LEM LEM' : ∀ ℓ → Set (lsuc ℓ)
LEM ℓ = (X : Set ℓ) → is-prop X → decidable X
LEM' ℓ = (X : Set ℓ) → subsingletonp X → singletonp X ＋ emptyp X

{-
  equivalence
-}

quasi-equiv : (A : Set ℓ₁) (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
quasi-equiv A B = Σ f ∶ (A → B) , Σ g ∶ (B → A) , f ∘ g ~ id × g ∘ f ~ id

invertible = quasi-equiv

-- witness x, f x = y
fiber : {X :  Set ℓ} {Y : Set ℓ₁} (f : X → Y) → Y → Set (ℓ ⊔ ℓ₁)
fiber {ℓ}{ℓ₁} {X}{Y} f y = Σ x ∶ X , f x ＝ y

fiber-point : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
            → fiber f y → X
fiber-point (x , p) = x

fiber-identity : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
               → (w : fiber f y) → f (fiber-point w) ＝ y
fiber-identity (x , p) = p

is-equiv : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
is-equiv {ℓ}{ℓ₁} {X}{Y} f = Π y ∶ Y , singletonp (fiber f y)

-- equivalence
_≃_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
X ≃ Y = Σ f ∶ (X → Y) , is-equiv f
infix 5 _≃_
