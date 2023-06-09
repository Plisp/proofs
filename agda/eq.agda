{-# OPTIONS --without-K --exact-split --safe #-}

{-
  basic equality results
-}

open import Agda.Primitive
open import logic

transport : {A : Set ℓ} (P : A → Set ℓ₁) {x y : A} → (x ＝ y) → (P x → P y)
transport{ℓ}{ℓ₁} {A} P {x}{y} p = ȷ (λ x y _ → P x → P y)
                                    (λ x → (id{ℓ₁} {P x}))
                                    x y p

ap : {A : Set ℓ} {B : Set ℓ₁} {x y : A}
   → (f : A → B) → (x ＝ y) → (f x ＝ f y)
ap{ℓ}{ℓ₁} {A}{B} {x}{y} f p = ȷ (λ x y _ → f x ＝ f y)
                                (λ x → refl (f x))
                                x y p

-- path notation
_∙_ : {A : Set ℓ} {x y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
_∙_ = trans
infixr 5 _∙_

apd : {X : Set ℓ} {A : X → Set ℓ₁} (f : (x : X) → A x) (x y : X)
      (p : x ＝ y) → transport A p (f x) ＝ f y
apd{ℓ}{ℓ₁} {X}{A} f x y p = ȷ (λ x y p → transport A p (f x) ＝ f y)
                              (λ x → refl (f x))
                              x y p

{-
  proof boilerplate
-}

ap2 : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ} {w x : A} {y z : B}
    → (f : A → B → C) → (w ＝ x) → (y ＝ z) → (f w y ＝ f x z)
ap2{ℓ₁}{ℓ₂}{ℓ} {A}{B}{C} {w}{x}{y}{z} f p q
  = (ap (λ x → f x y) p) ∙ (ap (λ y → f x y) q) -- f w y ＝ f x y ＝ f x z
-- ap2{ℓ₁}{ℓ₂}{ℓ} {A}{B}{C} {w}{x}{y}{z} f p q = ȷ (λ w x _ → f w y ＝ f x z)
--                                                (λ x → ȷ (λ y z _ → f x y ＝ f x z)
--                                                         (λ y → (refl (f x y)))
--                                                         y z q)
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
  hott chapter 2
-}

-- lemma 2.1.4
refl-refl : {A : Set ℓ} → (x : A) → refl x ＝ refl x
refl-refl x = refl (refl x)

refl∙p＝p : {A : Set ℓ} (x y : A) → (p : x ＝ y) → refl x ∙ p ＝ p
refl∙p＝p = ȷ (λ x y p → refl x ∙ p ＝ p) refl-refl

p∙iv＝refl : {A : Set ℓ} (x y : A) → (p : x ＝ y) → p ∙ (sym p) ＝ (refl x)
p∙iv＝refl = ȷ (λ x y p → p ∙ (sym p) ＝ (refl x)) refl-refl

sym-volution : {A : Set ℓ} (x y : A) → (p : x ＝ y) → sym (sym p) ＝ p
sym-volution = ȷ (λ x y p → sym (sym p) ＝ p) refl-refl

∙-assoc : {A : Set ℓ} (w x y z : A) → (p : w ＝ x) → (q : x ＝ y) → (r : y ＝ z)
        → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙-assoc w x y z p q r = ⅉ x (λ w (p : w ＝ x) → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)) lemma w p
  where
    lemma : (refl x ∙ q) ∙ r ＝ refl x ∙ (q ∙ r)
    lemma = (ap (λ x → x ∙ r) (refl∙p＝p x y q) ∙ sym (refl∙p＝p x z (q ∙ r)))

-- lemma 2.2.2
ap-id-p＝p : {A : Set ℓ} (x y : A) → (p : x ＝ y) → ap id p ＝ p
ap-id-p＝p{ℓ}{A} = ȷ (λ x y p → ap id p ＝ p) refl-refl

-- lemma 2.3.5 - 2.3.11

-- homotopy
_~_ : {X : Set ℓ} → {A : X → Set ℓ₁} → Π A → Π A → Set (ℓ ⊔ ℓ₁)
f ~ g = ∀ x → (f x ＝ g x)
infix 5 _~_

-- lemma 2.4.2

-- lemma 2.4.3 naturality

-- equivalence
quasi-equiv : (A : Set ℓ₁) → (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
quasi-equiv A B = Σ f ∶ (A → B) , Σ g ∶ (B → A) , (f ∘ g) ~ id × (g ∘ f) ~ id

-- lemma 2.4.12

{-
  hott chapter 3
-}

decidable : Set ℓ → Set ℓ
decidable A = A ＋ ¬ A

has-decidable-equality : Set ℓ → Set ℓ
has-decidable-equality A = (x y : A) → decidable (x ＝ y)
