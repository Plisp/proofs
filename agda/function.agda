{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Primitive
open import logic
open import bool
open import path
open import homotopy

contravariance : {P Q R : Set} → (Q → P) → (P → R) → (Q → R)
contravariance f g = g ∘ f

-- space: witnesses x' × f x' = y
fiber : {X :  Set ℓ} {Y : Set ℓ₁} (f : X → Y) → Y → Set (ℓ ⊔ ℓ₁)
fiber {X = X}{Y} f y = Σ x ∶ X , f x ＝ y

fiber-base : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
           → fiber f y → X
fiber-base (x , p) = x

fiber-id : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
         → (w : fiber f y) → f (fiber-base w) ＝ y
fiber-id (x , p) = p

surjective :{A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set (ℓ ⊔ ℓ₁)
surjective {A = A}{B} f = ∀ (y : B) → fiber f y

injective : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set (ℓ ⊔ ℓ₁)
injective {A = A}{B} f = ∀ (x y : A) → (f x ＝ f y) → (x ＝ y)

injective' : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set (ℓ ⊔ ℓ₁)
injective' {A = A}{B} f = ∀ (x y : A) → (x ≠ y) → (f x ≠ f y)

invertible : {A : Set ℓ} {B : Set ℓ₁} (f : A → B) → Set (ℓ ⊔ ℓ₁)
invertible {A = A}{B} f = Σ g ∶ (B → A) , g ∘ f ~ id × f ∘ g ~ id

{-
  mono and epi up to homotopy
-}

wmono : {A : Set ℓ} {B : Set ℓ₁} (f : A → B) → Set (lsuc (ℓ ⊔ ℓ₁))
wmono {ℓ}{ℓ₁}{A}{B} f = ∀{C : Set (ℓ ⊔ ℓ₁)} → (g h : C → A)
                        → (f ∘ g) ~ (f ∘ h) → g ~ h

wepi : {A : Set ℓ} {B : Set ℓ₁} (f : A → B) → Set (lsuc (ℓ ⊔ ℓ₁))
wepi {ℓ}{ℓ₁}{A}{B} f = ∀{C : Set (ℓ ⊔ ℓ₁)} → (g h : B → C)
                       → (g ∘ f) ~ (h ∘ f) → g ~ h

{-
  retracts, split mono and epi
-}

-- r ∘ s ＝ id , embedding then quotient , s ; r ＝ id
has-retraction : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
has-retraction {X = X}{Y} s = Σ r ∶ (Y → X) , r ∘ s ~ id

-- right inverse
has-section : {X : Set ℓ} {Y : Set ℓ₁} → (Y → X) → Set (ℓ ⊔ ℓ₁)
has-section {X = X}{Y} r = Σ s ∶ (X → Y) , r ∘ s ~ id

-- X type is a retract of Y
_◁_ : Set ℓ → Set ℓ₁ → Set (ℓ ⊔ ℓ₁)
X ◁ Y = Σ f ∶ (Y → X) , has-section f

retraction : {X : Set ℓ} {Y : Set ℓ₁} → X ◁ Y → (Y → X)
retraction (r , s , η) = r

section : {X : Set ℓ} {Y : Set ℓ₁} → X ◁ Y → (X → Y)
section (r , s , η) = s

is-retract : {X : Set ℓ} {Y : Set ℓ₁} → (p : X ◁ Y)
           → retraction p ∘ section p ~ id
is-retract (r , s , η) = η

refl◁ : (X : Set ℓ) → X ◁ X
refl◁ X = id , id , refl

_◁∙_ : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂} → X ◁ Y → Y ◁ Z → X ◁ Z
(r , s , η) ◁∙ (r' , s' , η') = r ∘ r' , s' ∘ s , λ x → ap r (η' (s x)) ∙ η x

_◁⟨_⟩_ : (X : Set ℓ) {Y : Set ℓ₁} {Z : Set ℓ₂} → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ x◁y ⟩ y◁z = x◁y ◁∙ y◁z
infixr 2 _◁⟨_⟩_

_◀ : (X : Set ℓ) → X ◁ X
X ◀ = refl◁ X
infix 3 _◀

{-
  theorems
-}

surj-comp : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
          → (f : A → B) → surjective f
          → (g : B → C) → surjective g
          → surjective (g ∘ f)
surj-comp {A = A}{B}{C} f pf g pg c
  = fiber-base pa , (ap g (fiber-id pa) ∙ fiber-id pb)
  where
    pb : fiber g c
    pb = pg c

    pa : fiber f (pr₁ pb)
    pa = pf (fiber-base pb)

surj-inj : {A : Set ℓ₁} {B : Set ℓ₂} → (f : A → B)
         → surjective f → Σ g ∶ (B → A) , injective g
surj-inj {A = A}{B} f surj
  = inj , λ x y p → sym＝ (fiber-id (surj x)) ∙ ap f p ∙ fiber-id (surj y)
  where
    inj : B → A
    inj b = fiber-base (surj b)

surj-inj-retract : {A : Set ℓ₁} {B : Set ℓ₂} → (f : A → B)
                 → (p : surjective f) → f ∘ pr₁ (surj-inj f p) ~ id
surj-inj-retract f p b = Σ.p2 (p b)

-- injection is weaker, injective' the contrapositive is even weaker

injective-injective' : {A : Set ℓ} {B : Set ℓ₂} → (f : A → B)
                     → injective f → injective' f
injective-injective' f p x y x≠y fx＝fy = x≠y (p x y fx＝fy)

inj-comp : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
         → (f : A → B) → injective f
         → (g : B → C) → injective g
         → injective (g ∘ f)
inj-comp f pf g pg = λ x y z → pf x y (pg (f x) (f y) z)

id-invertible : {X : Set ℓ} → invertible (id {ℓ}{X})
id-invertible {X = X} = id , refl , refl

inverse-invertible : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y}
                   → ((g , _) : invertible f) → invertible g
inverse-invertible {X = X}{Y} {f} (g , fg , gf) = f , gf , fg

invertible-∘ : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂} {f : X → Y} {f' : Y → Z}
             → invertible f' → invertible f → invertible (f' ∘ f)
-- middle terms cancel
invertible-∘ {X = X}{Y}{Z} {f}{f'} (g' , gf' , fg') (g , gf , fg) =
  g ∘ g' , (λ x → ap g (gf' (f x)) ∙ gf x) , λ z → ap f' (fg (g' z)) ∙ fg' z

-- XXX lack of cumulativity??
wmono-inj : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
          → wmono f → injective f
wmono-inj {A = A}{B} f p x y fx＝fy = lemma (λ _ → fx＝fy) (inr ⋆)
  where
    lemma : ((A × B ＋ 𝟙) → f x ＝ f y) → (A × B ＋ 𝟙) → x ＝ y
    lemma = p (λ _ → x) (λ _ → y)

inj-wmono : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
          → injective f → wmono f
inj-wmono {A = A}{B} f p g h fg~fh x = p (g x) (h x) (fg~fh x)

section-inj : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
            → has-retraction f → injective f
section-inj f (r , p) a1 a2 fa1＝fa2 = sym＝ (p a1) ∙ ap r fa1＝fa2 ∙ p a2

inj-no-section : Σ f ∶ (𝟘 → 𝟙) , injective f × ¬ has-retraction f
inj-no-section = (λ _ → ⋆) , (λ x ()) , λ z → pr₁ z ⋆

surj-wepi : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
          → surjective f → wepi f
surj-wepi {A = A}{B} f p g h gf~hf x
  = sym＝ (ap g (pr₂ lemma)) ∙ gf~hf (pr₁ lemma) ∙ ap h (pr₂ lemma)
  where
    lemma : Σ a ∶ A , f a ＝ x
    lemma = p x

-- true if you consider all sets, take non-contr codomain for g,h and differ on F
-- wepi-no-surj : Σ f ∶ (𝟙 → Bool) , wepi f × ¬ surjective f
-- wepi-no-surj = (λ z → true) , (λ g h p b → {!!}) , {!!}

surj-retraction : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
                → surjective f → has-section f
surj-retraction f fib = (λ b → fiber-base (fib b)) , λ a → fiber-id (fib a)

retraction-surj : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
                → has-section f → surjective f
retraction-surj f (s , p) b = s b , p b

-- invertible is very strong

invertible-section : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
                   → invertible f → has-retraction f
invertible-section f (g , gf , fg) = g , gf

invertible-retraction : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
                      → invertible f → has-section f
invertible-retraction f (g , gf , fg) = g , fg

-- can we weaken surjectivity to weak epi? probably not
inj-surj-invertible : {A : Set ℓ} {B : Set ℓ₁} (f : A → B)
                    → injective f → surjective f
                    → invertible f
inj-surj-invertible f inj fib = (λ b → fiber-base (fib b))
                              , (λ a → inj _ _ (fiber-id (fib (f a))))
                              , λ b → fiber-id (fib b)

-- XXX another cumulativity issue, so use ℓ for B as well
wepi-section-invertible : {A : Set ℓ} {B : Set ℓ} (f : A → B)
                        → has-retraction f → wepi f
                        → invertible f
wepi-section-invertible {A = A}{B} f (r , p) ep = r , p , ep _ (id {T = B}) lemma
  where
    lemma : (f ∘ r ∘ f) ~ f
    lemma a = ap f (p a)

-- what if they are not known to be the same?
-- sect-retr-invert : {A : Set ℓ} {B : Set ℓ₁} (f g : A → B)
--                  → has-retraction f → has-section g
--                  → invertible f
-- sect-retr-invert f g (r , pf) (s , pg) = {!!} , {!!} , {!!}

{-
  extensional
-}

ext-surjective : {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} → (f : A → (B → C))
               → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
ext-surjective {A = A}{B}{C} f = ∀ (g : B → C) → Σ a ∶ A , f a ~ g

surj-ext-surj : {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} → (f : A → (B → C))
              → surjective f → ext-surjective f
surj-ext-surj f p x = Σ.p1 (p x) , id~ (Σ.p2 (p x))

has-ext-section : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂}
                → (Z → (X → Y)) → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
has-ext-section {X = X}{Y}{Z} r
  = Σ s ∶ ((X → Y) → Z) , ∀ f → (r (s f)) ~ f

ext-retraction-surj : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
                    → (r : A → (B → C)) → has-ext-section r
                    → ext-surjective r
ext-retraction-surj r (s , p) = λ f → (s f , p f)
