{-# OPTIONS --without-K --exact-split --safe #-}

{-
  basic equality results
-}

open import logic

lhs : {A : Set ℓ} {x y : A} → (x ＝ y) → A
lhs{ℓ} {A} {x}{y} p = x

rhs : {A : Set ℓ} {x y : A} → (x ＝ y) → A
rhs{ℓ} {A} {x}{y} p = y

transport : {A : Set ℓ} (P : A → Set ℓ₁) {x y : A} → (x ＝ y) → (P x → P y)
transport{ℓ}{ℓ₁} {A} P {x}{y} p = ȷ (λ x y _ → P x → P y)
                                    (λ x → (id{ℓ₁} {P x}))
                                    x y p

ap : {A : Set ℓ} {B : Set ℓ₁} {x y : A}
   → (f : A → B) → (x ＝ y) → (f x ＝ f y)
ap{ℓ}{ℓ₁} {A}{B} {x}{y} f p = ȷ (λ x y _ → f x ＝ f y)
                                (λ x → refl (f x))
                                x y p

ap-id-p＝p : {A : Set ℓ} {x y : A} → (p : x ＝ y) → ap id p ＝ p
ap-id-p＝p{ℓ}{A} {x}{y} = ȷ (λ x y p → ap id p ＝ p)
                           (λ x → refl (refl x)) x y

-- path notation
_∙_ : {A : Set ℓ} {x y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
p ∙ q = transport (λ y → (lhs p) {- x -} ＝ y) q p
--p ∙ q = transport (λ x → x ＝ (rhs q)) (sym p) q
infixr 5 _∙_

refl∙p＝p : {A : Set ℓ} {x y : A} → (p : x ＝ y) → refl x ∙ p ＝ p
refl∙p＝p{ℓ}{A} {x}{y} = ȷ (λ x y p → refl x ∙ p ＝ p) (λ x → refl (refl x)) x y

{-
  proof boilerplate
-}

ap2 : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ} {w x : A} {y z : B}
    → (f : A → B → C) → (w ＝ x) → (y ＝ z) → (f w y ＝ f x z)
ap2{ℓ₁}{ℓ₂}{ℓ} {A}{B}{C} {w}{x}{y}{z} f p q
  = (ap (λ x → f x y) p) ∙ (ap (λ y → f x y) q) -- f w y ＝ f x y ＝ f x z
-- ap2{ℓ₁}{ℓ₂}{ℓ} {A}{B}{C} {w}{x}{y}{z} f p q = ȷ (λ w x _ → f w y ＝ f x z)
--                                                 (λ x → ȷ (λ y z _ → f x y ＝ f x z)
--                                                          (λ y → (refl (f x y)))
--                                                          y z q)
--                                                 w x p

ap4 : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ₄} {E : Set ℓ}
    → {a e : A} {b f : B} {c g : C} {d h : D}
    → (fn : A → B → C → D → E)
    → (a ＝ e) → (b ＝ f) → (c ＝ g) → (d ＝ h)
    → (fn a b c d ＝ fn e f g h)
ap4{ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄}{ℓ} {A}{B}{C}{D}{E} {a}{e}{b}{f}{c}{g}{d}{h} fn p q r s
  = (ap (λ x → fn x b c d) p) ∙ (ap (λ x → fn e x c d) q) ∙
    (ap (λ x → fn e f x d) r) ∙ (ap (λ x → fn e f g x) s)

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

𝟙≠𝟘 : 𝟙 ≠ 𝟘 -- (𝟙 = 𝟘) → ⊥
𝟙≠𝟘 p = transport id p ⋆

{-
  hott
-}

has-decidable-equality : Set ℓ → Set ℓ
has-decidable-equality A = (x y : A) → decidable (x ＝ y)
