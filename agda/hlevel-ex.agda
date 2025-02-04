{-# OPTIONS --without-K --exact-split --safe #-}

{-
  univalent math, hott chapter 3
-}

open import Agda.Primitive
open import logic
open import path
open import hlevel

𝟙-is-singleton : is-contr 𝟙
𝟙-is-singleton = ⋆ , ind⊤ (λ x → ⋆ ＝ x) (refl ⋆)

𝟙-subsingleton : (a b : 𝟙) → a ＝ b
𝟙-subsingleton = singletons-are-subsingletons 𝟙 𝟙-is-singleton

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = ind⊥ (λ x → (x ＝ y)) x

𝟘-is-set : is-set 𝟘
𝟘-is-set = subsingleton→set 𝟘 𝟘-is-subsingleton

to-subtype-＝ : {X : Set ℓ} {A : X → Set ℓ₁}
               {x y : X} {a : A x} {b : A y}
             → ((x : X) → is-subsingleton (A x))
             → x ＝ y
             → (x , a) ＝ (y , b)
to-subtype-＝ {ℓ}{ℓ₁} {X}{A} {x}{y}{a}{b} f p = Σ＝ (p , f y (transport A p a) b)

Σ-is-subsingleton : {X : Set ℓ} {A : X → Set ℓ₁}
                  → is-subsingleton X
                  → ((x : X) → is-subsingleton (A x))
                  → is-subsingleton (Σ A)
Σ-is-subsingleton ss f (x , ax) (y , ay) = to-subtype-＝ f (ss x y)

×-is-singleton : {X : Set ℓ} {Y : Set ℓ₁}
               → is-contr X
               → is-contr Y
               → is-contr (X × Y)
×-is-singleton (cx , centrality-x) (cy , centrality-y)
  = (cx , cy) , λ x → ×＝ (centrality-x (fst x) , centrality-y (snd x))

×-is-subsingleton : {X : Set ℓ} {Y : Set ℓ₁}
                  → is-subsingleton X
                  → is-subsingleton Y
                  → is-subsingleton (X × Y)
×-is-subsingleton fx fy (x1 , x2) (y1 , y2) = ×＝ (fx x1 y1 , fy x2 y2)

{-
  TODO hedberg
-}
