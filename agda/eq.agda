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

apd : {X : Set ℓ} {A : X → Set ℓ₁} (f : (x : X) → A x)
    → (x y : X) (p : x ＝ y) → transport A p (f x) ＝ f y
apd{ℓ}{ℓ₁} {X}{A} f = ȷ (λ x y p → transport A p (f x) ＝ f y)
                        (λ x → refl (f x))

-- path notation
_∙_ : {A : Set ℓ} {x y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
_∙_ = trans
infixr 5 _∙_

{-
  proof boilerplate
-}

-- ap2 : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ} {w x : A} {y z : B}
--     → (f : A → B → C) → (w ＝ x) → (y ＝ z) → (f w y ＝ f x z)
-- ap2{ℓ₁}{ℓ₂}{ℓ} {A}{B}{C} {w}{x}{y}{z} f p q
--   = (ap (λ x → f x y) p) ∙ (ap (λ y → f x y) q)
-- ap2{ℓ₁}{ℓ₂}{ℓ} {A}{B}{C} {w}{x}{y}{z} f p q = ȷ (λ w x _ → f w y ＝ f x z)
--                                                (λ x → ȷ (λ y z _ → f x y ＝ f x z)
--                                                         (λ y → (refl (f x y)))
--                                                         y z q)
--                                                 w x p

-- ap4 : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ₄} {E : Set ℓ}
--     → {a e : A} {b f : B} {c g : C} {d h : D}
--     → (fn : A → B → C → D → E)
--     → (a ＝ e) → (b ＝ f) → (c ＝ g) → (d ＝ h)
--     → (fn a b c d ＝ fn e f g h)
-- ap4{ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄}{ℓ} {A}{B}{C}{D}{E} {a}{e}{b}{f}{c}{g}{d}{h} fn p q r s
--   = (ap (λ x → fn x b c d) p) ∙ (ap (λ x → fn e x c d) q) ∙
--     (ap (λ x → fn e f x d) r) ∙ (ap (λ x → fn e f g x) s)

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

-- ∙ lemmas
refl-refl : {A : Set ℓ} → (x : A) → refl x ＝ refl x
refl-refl x = refl (refl x)

p＝refl∙p : {A : Set ℓ} {x y : A} (p : x ＝ y) → p ＝ refl x ∙ p
p＝refl∙p{ℓ}{A} {x}{y} = ȷ (λ x y p → p ＝ refl x ∙ p) refl-refl x y

p∙refl＝p : {A : Set ℓ} {x y : A} (p : x ＝ y) → p ∙ refl y ＝ p
p∙refl＝p{ℓ}{A} {x}{y} = ȷ (λ x y p → p ∙ refl y ＝ p) refl-refl x y

p∙iv＝refl : {A : Set ℓ} {x y : A} (p : x ＝ y) → p ∙ (sym p) ＝ (refl x)
p∙iv＝refl{ℓ}{A} {x}{y} = ȷ (λ x y p → p ∙ (sym p) ＝ (refl x)) refl-refl x y

iv∙p＝refl : {A : Set ℓ} {x y : A} (p : x ＝ y) → (sym p) ∙ p ＝ (refl y)
iv∙p＝refl{ℓ}{A} {x}{y} = ȷ (λ x y p → (sym p) ∙ p ＝ (refl y)) refl-refl x y

sym-volution : {A : Set ℓ} {x y : A} (p : x ＝ y) → sym (sym p) ＝ p
sym-volution{ℓ}{A} {x}{y} = ȷ (λ x y p → sym (sym p) ＝ p) refl-refl x y

∙-assoc : {A : Set ℓ} {w x y z : A} (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
        → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙-assoc{ℓ}{A} {w}{x}{y}{z} p q r
  = ⅉ y (λ z (r : y ＝ z) → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)) lemma z r
  where
    lemma : (p ∙ q) ∙ (refl y) ＝ p ∙ (q ∙ refl y)
    lemma = p∙refl＝p (p ∙ q) ∙ ap (λ q → p ∙ q) (sym (p∙refl＝p q))

-- ap lemmas
apf-homo-∙ : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B)
           → {x y z : A} (p : x ＝ y) (q : y ＝ z)
           → ap f (p ∙ q) ＝ ap f p ∙ ap f q
apf-homo-∙ f {x}{y}{z} p q = ⅉ y (λ z q → ap f (p ∙ q) ＝ ap f p ∙ ap f q)
                                 (ȷ (λ x y p → ap f (p ∙ refl y)
                                             ＝ ap f p ∙ ap f (refl y))
                                    (λ x → refl-refl (f x))
                                    x y p)
                                 z q

ap-commut-sym : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
              → {x y : A} (p : x ＝ y)
              → ap f (sym p) ＝ sym (ap f p)
ap-commut-sym f {x}{y} = ȷ (λ x y p → ap f (sym p) ＝ sym (ap f p))
                           (λ x → refl (refl (f x)))
                           x y

ap-homo-∘ : {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} → (f : A → B) (g : B → C)
          → {x y : A} (p : x ＝ y)
          → ap (g ∘ f) p ＝ (ap g ∘ ap f) p
ap-homo-∘ f g {x}{y} = ȷ (λ x y p → ap (g ∘ f) p ＝ ap g (ap f p))
                         (λ x → refl (refl ((g ∘ f) x)))
                         x y

ap-id-p＝p : {A : Set ℓ} {x y : A} → (p : x ＝ y) → ap id p ＝ p
ap-id-p＝p{ℓ}{A} {x}{y} = ȷ (λ x y p → ap id p ＝ p) refl-refl x y

-- transport lemmas
transport-∙ : {A : Set ℓ} {P : A → Set ℓ₁} → {x y z : A} (p : x ＝ y) (q : y ＝ z)
            → (u : P x) → transport P q (transport P p u) ＝ transport P (p ∙ q) u
transport-∙{ℓ}{ℓ₁} {A}{P} {x}{y}{z} p q u
  = ⅉ y (λ z q → transport P q (transport P p u) ＝ transport P (p ∙ q) u)
        (ⅉ x (λ y p → transport P (refl y) (transport P p u)
                    ＝ transport P (p ∙ refl y) u)
             (refl u)
             y p)
        z q

transport-∘ : {A : Set ℓ} {B : Set ℓ₁} {P : B → Set ℓ₂} → (f : A → B)
            → {x y : A} (p : x ＝ y)
            → (u : P (f x)) → transport (P ∘ f) p u ＝ transport P (ap f p) u
transport-∘{ℓ}{ℓ₁}{ℓ₂} {A}{B}{P} f {x}{y}
  = ȷ (λ x y p → ∀ u → transport (P ∘ f) p u ＝ transport P (ap f p) u)
      (λ x → λ u → refl u)
      x y

transport-fam : {A : Set ℓ} {P Q : A → Set ℓ₁} → (f : Π x ∶ A , (P x → Q x))
              → {x y : A} (p : x ＝ y)
              → (u : P x) → transport Q p (f x u) ＝ f y (transport P p u)
transport-fam{ℓ}{ℓ₁} {A}{P}{Q} f {x}{y}
  = ȷ (λ x y p → ∀ u → transport Q p (f x u) ＝ f y (transport P p u))
      (λ x → λ u → refl (f x u))
      x y

{-
  homotopy
-}

_~_ : {X : Set ℓ} {A : X → Set ℓ₁} → Π A → Π A → Set (ℓ ⊔ ℓ₁)
f ~ g = ∀ x → (f x ＝ g x)
infix 5 _~_

-- equivalence relation
~refl : {A : Set ℓ} {P : A → Set ℓ₁} → (f : Π x ∶ A , P x) → (f ~ f)
~refl f = λ x → refl (f x)

~sym : {A : Set ℓ} {P : A → Set ℓ₁} → {f g : Π x ∶ A , P x}
     → (f ~ g) → (g ~ f)
~sym hom = λ x → sym (hom x)

~trans : {A : Set ℓ} {P : A → Set ℓ₁} → {f g h : Π x ∶ A , P x}
       → (f ~ g) → (g ~ h) → (f ~ h)
~trans homf homg = λ x → trans (homf x) (homg x)

-- naturality
~nat : {A : Set ℓ} {B : Set ℓ₁}
     → (f g : A → B) (H : f ~ g) → {x y : A} (p : x ＝ y)
     → H x ∙ ap g p ＝ ap f p ∙ H y
~nat f g H {x}{y} = ȷ (λ x y p → H x ∙ ap g p ＝ ap f p ∙ H y)
                      (λ x → p∙refl＝p (H x) ∙ p＝refl∙p (H x))
                      x y

~commut : {A : Set ℓ} → (f : A → A) (H : f ~ id)
        → (x : A) → H (f x) ＝ ap f (H x)
~commut f H x = simplify (~nat f id H {f x} {x} (H x))
  where
    lemma1 : H (f x) ∙ (H x) ＝ H (f x) ∙ ap id (H x)
    lemma1 = ap (λ e → H (f x) ∙ e) (sym (ap-id-p＝p (H x)))

    whisker : H (f x) ∙ (H x) ＝ ap f (H x) ∙ (H x)
            → H (f x) ∙ (H x) ∙ (sym (H x)) ＝ ap f (H x) ∙ (H x) ∙ (sym (H x))
    whisker p = sym (∙-assoc (H (f x)) (H x) (sym (H x)))
              ∙ ap (λ e → e ∙ sym (H x)) p
              ∙ ∙-assoc (ap f (H x)) (H x) (sym (H x))

    lemma3 : H (f x) ＝ H (f x) ∙ (H x) ∙ (sym (H x))
    lemma3 = sym (p∙refl＝p (H (f x)))
           ∙ ap (λ e → H (f x) ∙ e) (sym (p∙iv＝refl (H x)))

    lemma4 : ap f (H x) ∙ (H x) ∙ (sym (H x)) ＝ ap f (H x)
    lemma4 = ap (λ e → ap f (H x) ∙ e) (p∙iv＝refl (H x)) ∙ (p∙refl＝p (ap f (H x)))

    simplify : H (f x) ∙ ap id (H x) ＝ ap f (H x) ∙ (H x) → _
    simplify p = lemma3 ∙ whisker (lemma1 ∙ p) ∙ lemma4

-- equivalence
quasi-equiv : (A : Set ℓ₁) (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
quasi-equiv A B = Σ f ∶ (A → B) , Σ g ∶ (B → A) , (f ∘ g) ~ id × (g ∘ f) ~ id
