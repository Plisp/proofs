{-# OPTIONS --without-K --exact-split --safe #-}

{-
  univalent math, hott chapter 3
-}

open import logic
open import eq

{-
  propositions
-}

is-center : (X : Set ℓ) → X → Set ℓ
is-center X c = (x : X) → c ＝ x

is-singleton : Set ℓ → Set ℓ
is-singleton X = Σ c ∶ X , is-center X c

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , ⊤-ind (λ x → ⋆ ＝ x) (refl ⋆)

center : (X : Set ℓ) → is-singleton X → X
center X (c , p) = c

centerp : (X : Set ℓ) (i : is-singleton X) (x : X) → center X i ＝ x
centerp X (c , p) = p

-- (subtype) singletons but maybe not inhabited
is-subsingleton : Set ℓ → Set ℓ
is-subsingleton X = (x y : X) → x ＝ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = ⊥-ind (λ x → (x ＝ y)) x

is-prop = is-subsingleton

singletone→subsingleton : (X : Set ℓ) → is-singleton X → is-subsingleton X
singletone→subsingleton X (c , p) x y = sym (p x) ∙ p y

pointed-subsingleton→singleton : (X : Set ℓ) X → is-subsingleton X → is-singleton X
pointed-subsingleton→singleton X x s = (x , s x)

{-
  hlevel 0
-}

is-set : Set ℓ → Set ℓ
is-set X = (x y : X) → is-subsingleton (x ＝ y)

{-
  decidable
-}

decidable : Set ℓ → Set ℓ
decidable A = A ＋ ¬ A

has-decidable-equality : Set ℓ → Set ℓ
has-decidable-equality A = (x y : A) → decidable (x ＝ y)
