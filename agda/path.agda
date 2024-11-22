{-# OPTIONS --without-K --exact-split --safe #-}

{-
  equality
-}

open import Agda.Primitive
open import logic

-- matching gives clearer computation rule, proved by Cockx to be same in without-K
sym＝ : {A : Set ℓ} {x y : A} → (x ＝ y) → (y ＝ x)
sym＝ (refl x) = refl x

-- but here's how to use ȷ anyways
trans＝ : {A : Set ℓ} {x y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
trans＝ {A = A} {x}{y}{z} p = ȷ (λ x y _ → y ＝ z → x ＝ z)
                               (λ x → (ȷ (λ x z _ → x ＝ z)
                                         (λ x → refl x)
                                         x z))
                              x y p

-- path notation, simpler computation rule for agda
_∙_ : {A : Set ℓ} {x y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
(refl x) ∙ (refl y) = refl x
infixr 5 _∙_

transport : {A : Set ℓ} (P : A → Set ℓ₁) {x y : A} → (x ＝ y) → (P x → P y)
transport P (refl _) = id
-- transport {ℓ}{ℓ₁} {A} P {x}{y} p = ȷ (λ x y _ → P x → P y)
--                                      (λ x → (id{ℓ₁} {P x}))
--                                      x y p
subst = transport

ap : {A : Set ℓ} {B : Set ℓ₁} {x y : A}
   → (f : A → B) → (x ＝ y) → (f x ＝ f y)
ap f (refl x) = refl (f x)

-- families respect equality, A x transports to an 'equal' A y
-- if equivalences generate a base, equality is the discrete topology
apd : {X : Set ℓ} {A : X → Set ℓ₁} (f : (x : X) → A x)
    → {x y : X} (p : x ＝ y) → transport A p (f x) ＝ f y
-- apd {ℓ}{ℓ₁} {X}{A} f {x}{y} p = ȷ (λ x y p → transport A p (f x) ＝ f y)
--                                   (λ x → refl (f x))
--                                   x y p
apd f (refl x) = refl (f x)

{-
  proof boilerplate
-}

ap₂ : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ} {w x : A} {y z : B}
    → (f : A → B → C) → (w ＝ x) → (y ＝ z) → (f w y ＝ f x z)
ap₂ {A = A}{B}{C} {w}{x}{y}{z} f p q = ap (λ x → f x y) p ∙ ap (f x) q

-- ap4 : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ₄} {E : Set ℓ}
--     → {a e : A} {b f : B} {c g : C} {d h : D}
--     → (fn : A → B → C → D → E)
--     → (a ＝ e) → (b ＝ f) → (c ＝ g) → (d ＝ h)
--     → (fn a b c d ＝ fn e f g h)
-- ap4 {ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄}{ℓ} {A}{B}{C}{D}{E} {a}{e}{b}{f}{c}{g}{d}{h} fn p q r s
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
≠-sym fp = fp ∘ sym＝

𝟙≠𝟘 : 𝟙 ≠ 𝟘 -- (𝟙 = 𝟘) → ⊥
𝟙≠𝟘 p = transport id p ⋆

{-
  hott chapter 2
-}

-- ∙ lemmas
refl-refl : {A : Set ℓ} → (x : A) → refl x ＝ refl x
refl-refl x = refl (refl x)

p＝refl∙p : {A : Set ℓ} {x y : A} (p : x ＝ y) → p ＝ refl x ∙ p
p＝refl∙p {A = A} {x}{y} = ȷ (λ x y p → p ＝ refl x ∙ p) refl-refl x y

p∙refl＝p : {A : Set ℓ} {x y : A} (p : x ＝ y) → p ∙ refl y ＝ p
p∙refl＝p {A = A} {x}{y} = ȷ (λ x y p → p ∙ refl y ＝ p) refl-refl x y

p∙iv＝refl : {A : Set ℓ} {x y : A} (p : x ＝ y) → p ∙ (sym＝ p) ＝ (refl x)
p∙iv＝refl {A = A} {x}{y} = ȷ (λ x y p → p ∙ (sym＝ p) ＝ (refl x)) refl-refl x y

iv∙p＝refl : {A : Set ℓ} {x y : A} (p : x ＝ y) → (sym＝ p) ∙ p ＝ (refl y)
iv∙p＝refl {A = A} {x}{y} = ȷ (λ x y p → (sym＝ p) ∙ p ＝ (refl y)) refl-refl x y

-- sym is an automorphism on A's groupoid
sym-∙ : {A : Set ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z)
      → sym＝ (p ∙ q) ＝ (sym＝ q ∙ sym＝ p)
sym-∙ (refl y) (refl y) = refl (refl y)

sym-volution : {A : Set ℓ} {x y : A} (p : x ＝ y) → sym＝ (sym＝ p) ＝ p
sym-volution {A = A} {x}{y} = ȷ (λ x y p → sym＝ (sym＝ p) ＝ p) refl-refl x y

assoc∙ : {A : Set ℓ} {w x y z : A} (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
        → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
assoc∙ {A = A} {w}{x}{y}{z} p q r
  = ⅉ y (λ z (r : y ＝ z) → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)) lemma z r
  where
    lemma : (p ∙ q) ∙ (refl y) ＝ p ∙ (q ∙ refl y)
    lemma = p∙refl＝p (p ∙ q) ∙ ap (λ q → p ∙ q) (sym＝ (p∙refl＝p q))

lcancel∙ : {A : Set ℓ} {x y z : A} (p : x ＝ y) (q r : y ＝ z)
         → (p ∙ q ＝ p ∙ r) → (q ＝ r)
lcancel∙ {A = A} {x}{y}{z} p q r pqr = lemma q ∙ whisker ∙ sym＝ (lemma r)
  where
    whisker : (sym＝ p) ∙ (p ∙ q) ＝ (sym＝ p) ∙ (p ∙ r)
    whisker = ap (λ e → (sym＝ p) ∙ e) pqr

    lemma : (q : y ＝ z) → q ＝ (sym＝ p) ∙ (p ∙ q)
    lemma q = p＝refl∙p q
            ∙ ap (λ r → r ∙ q) (sym＝ (iv∙p＝refl p))
            ∙ assoc∙ (sym＝ p) p q

rcancel∙ : {A : Set ℓ} {x y z : A} (p : y ＝ z) (q r : x ＝ y)
         → (q ∙ p ＝ r ∙ p) → (q ＝ r)
rcancel∙ {A = A} {x}{y}{z} p q r pqr = lemma q ∙ whisker ∙ sym＝ (lemma r)
  where
    whisker :  (q ∙ p) ∙ (sym＝ p) ＝ (r ∙ p) ∙ (sym＝ p)
    whisker = ap (λ e → e ∙ (sym＝ p)) pqr

    lemma : (q : x ＝ y) → q ＝ (q ∙ p) ∙ (sym＝ p)
    lemma q = sym＝ (p∙refl＝p q)
            ∙ ap (λ r → q ∙ r) (sym＝ (p∙iv＝refl p))
            ∙ sym＝ (assoc∙ q p (sym＝ p))

-- ap lemmas
apf-∙ : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B)
      → {x y z : A} (p : x ＝ y) (q : y ＝ z)
      → ap f (p ∙ q) ＝ ap f p ∙ ap f q -- homomorphism
apf-∙ f {x}{y}{z} p q = ⅉ y (λ z q → ap f (p ∙ q) ＝ ap f p ∙ ap f q)
                            (ȷ (λ x y p → ap f (p ∙ refl y)
                                        ＝ ap f p ∙ ap f (refl y))
                               (λ x → refl-refl (f x))
                               x y p)
                            z q

commut-sym-ap : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
              → {x y : A} (p : x ＝ y)
              → ap f (sym＝ p) ＝ sym＝ (ap f p)
commut-sym-ap f {x}{y} = ȷ (λ x y p → ap f (sym＝ p) ＝ sym＝ (ap f p))
                           (λ x → refl (refl (f x)))
                           x y

ap-∘ : {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} → (f : A → B) (g : B → C)
     → {x y : A} (p : x ＝ y)
     → ap (g ∘ f) p ＝ (ap g ∘ ap f) p
ap-∘ f g {x}{y} = ȷ (λ x y p → ap (g ∘ f) p ＝ ap g (ap f p))
                    (λ x → refl (refl ((g ∘ f) x)))
                    x y

ap-id-p＝p : {A : Set ℓ} {x y : A} → (p : x ＝ y) → ap id p ＝ p
ap-id-p＝p {A = A} {x}{y} = ȷ (λ x y p → ap id p ＝ p) refl-refl x y

-- transport lemmas
transport-const : {A : Set ℓ} {B : Set ℓ₁} (b : B)
                → {x y : A} (p : x ＝ y)
                → transport (λ _ → B) p b ＝ b
transport-const {A = A}{B} b {x}{y} = ȷ (λ x y p → transport (λ _ → B) p b ＝ b)
                                        (λ x → refl b)
                                        x y

transport-sym-p : {A : Set ℓ} {P : A → Set ℓ₁} {x y : A} (p : x ＝ y)
                → transport P (sym＝ p) ∘ transport P p ＝ id
transport-sym-p {A = A}{P} {x}{y} p
  = ȷ (λ x y p → transport P (sym＝ p) ∘ transport P p ＝ id)
      (λ x → refl id) -- transport P refl = id
      x y p

transport-p-sym : {A : Set ℓ} {P : A → Set ℓ₁} {x y : A} (p : x ＝ y)
                → transport P p ∘ transport P (sym＝ p) ＝ id
transport-p-sym {A = A}{P} {x}{y} p
  = ȷ (λ x y p → transport P p ∘ transport P (sym＝ p) ＝ id)
      (λ x → refl id) -- transport P refl = id
      x y p

transport∙ : {A : Set ℓ} {P : A → Set ℓ₁} → {x y z : A} (p : x ＝ y) (q : y ＝ z)
           → (u : P x) → transport P q (transport P p u) ＝ transport P (p ∙ q) u
transport∙ {A = A}{P} {x}{y}{z} p q u
  = ⅉ y (λ z q → transport P q (transport P p u) ＝ transport P (p ∙ q) u)
        (ⅉ x (λ y p → transport P (refl y) (transport P p u)
                    ＝ transport P (p ∙ refl y) u)
             (refl u)
             y p)
        z q

transport∘ : {A : Set ℓ} {B : Set ℓ₁} {P : B → Set ℓ₂} → (f : A → B)
           → {x y : A} (p : x ＝ y) (u : P (f x))
           → transport (P ∘ f) p u ＝ transport P (ap f p) u
transport∘ {ℓ}{ℓ₁}{ℓ₂} {A}{B}{P} f {x}{y}
  = ȷ (λ x y p → ∀ u → transport (P ∘ f) p u ＝ transport P (ap f p) u)
      (λ x → λ u → refl u)
      x y

transport-fam : {A : Set ℓ} {P Q : A → Set ℓ₁} → (f : Π x ∶ A , (P x → Q x))
              → {x y : A} (p : x ＝ y) (u : P x)
              → transport Q p (f x u) ＝ f y (transport P p u)
transport-fam {A = A}{P}{Q} f {x}{y}
  = ȷ (λ x y p → ∀ u → transport Q p (f x u) ＝ f y (transport P p u))
      (λ x → λ u → refl (f x u))
      x y

transport-startpoint : {A : Set ℓ} {a x y : A} → (p : x ＝ y) (q : a ＝ x)
                     → transport (λ - → a ＝ -) p q ＝ q ∙ p
transport-startpoint {A = A} {a}{x}{y} p q
  = ȷ (λ x y p → (q : a ＝ x) → transport (λ - → a ＝ -) p q ＝ q ∙ p)
      (λ x → λ q → sym＝ (p∙refl＝p q))
      x y p q

{-
  equality in ×
-}

×＝ : {X : Set ℓ} {Y : Set ℓ₁} {z t : X × Y}
   → (fst z ＝ fst t) × (snd z ＝ snd t) → z ＝ t
×＝ {X = X}{Y} {z1 , z2} {t1 , t2} (refl z1 , refl z2) = refl (z1 , z2)

from-×＝ : {X : Set ℓ} {Y : Set ℓ₁} {z t : X × Y}
        → z ＝ t → (fst z ＝ fst t) × (snd z ＝ snd t)
from-×＝ {X = X}{Y} {z}{t} (refl (x , y)) = (refl x , refl y)

{-
  equality in Σ
-}

Σ＝ : {X : Set ℓ} {A : X → Set ℓ₁} {σ τ : Σ A}
   → Σ p ∶ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ
   → σ ＝ τ
Σ＝ (refl x , refl a) = refl (x , a)

from-Σ＝ : {X : Set ℓ} {A : X → Set ℓ₁} {σ τ : Σ A}
        → σ ＝ τ
        → Σ p ∶ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ
from-Σ＝ (refl (x , a)) = (refl x , refl a)
