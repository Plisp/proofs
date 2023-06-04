{-# OPTIONS --without-K --exact-split --safe #-}

{-
  basic equality results
-}

open import logic

lhs : {A : Set ℓ} {x y : A} → (x ＝ y) → A
lhs{ℓ} {A} {x} {y} p = x

rhs : {A : Set ℓ} {x y : A} → (x ＝ y) → A
rhs{ℓ} {A} {x} {y} p = y

ap : {A : Set ℓ} {B : Set ℓ₁} {x y : A}
   → (f : A → B) → (x ＝ y) → (f x ＝ f y)
ap{ℓ}{ℓ₁} {A} {B} {x} {y} f p = ȷ (λ y → f x ＝ f y) p (refl (f x))

transport : {A : Set ℓ} (P : A → Set ℓ₁) {x y : A} → (x ＝ y) → (P x → P y)
transport{ℓ}{ℓ₁} {A} P {x} {y} p = ȷ (λ y → P x → P y) p (id{ℓ₁} {P x})

-- path notation
_∙_ : {A : Set ℓ} {x y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
p ∙ q = transport (λ y → (lhs p) {- x -} ＝ y) q p
--p ∙ q = transport (λ x → x ＝ (rhs q)) (sym p) q
infixr 5 _∙_

{-
  proof boilerplate
-}

begin_ : {A : Set ℓ} → {x y : A} → x ＝ y → x ＝ y
begin p = p
infix 1 begin_

_∎ : {A : Set ℓ} → (x : A) → x ＝ x
x ∎ = refl x
infix 3 _∎

_=⟨_⟩_ : {A : Set ℓ} → (x : A) → {y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
x =⟨ p ⟩ q = p ∙ q
infixr 2 _=⟨_⟩_

_=⟨⟩_ : {A : Set ℓ} → (x : A) → {y : A} → x ＝ y → x ＝ y
x =⟨⟩ q = x =⟨ refl x ⟩ q
infixr 2 _=⟨⟩_

{-
  negative equality
-}

_≠_ : {X : Set ℓ} → X → X → Set ℓ
x ≠ y = ¬(x ＝ y)

≠-sym : {A : Set ℓ} {x y : A} → (x ≠ y) → (y ≠ x)
≠-sym fp = fp ∘ sym

𝟙-neq-𝟘 : 𝟙 ≠ 𝟘 -- (𝟙 = 𝟘) → ⊥
𝟙-neq-𝟘 p = transport id p ⋆

{-
  hott
-}

has-decidable-equality : Set ℓ → Set ℓ
has-decidable-equality A = (x y : A) → decidable (x ＝ y)
