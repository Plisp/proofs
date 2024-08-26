{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Primitive
open import logic
open import path

open import homotopy

-- space: witnesses x' × f x' = y
fiber : {X :  Set ℓ} {Y : Set ℓ₁} (f : X → Y) → Y → Set (ℓ ⊔ ℓ₁)
fiber {ℓ}{ℓ₁} {X}{Y} f y = Σ x ∶ X , f x ＝ y

fiber-base : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
           → fiber f y → X
fiber-base (x , p) = x

fiber-id : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
         → (w : fiber f y) → f (fiber-base w) ＝ y
fiber-id (x , p) = p

surjective :{A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set (ℓ ⊔ ℓ₁)
surjective {ℓ₁}{ℓ₂} {A}{B} f = ∀ (y : B) → fiber f y

injective : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set (ℓ ⊔ ℓ₁)
injective {ℓ₁}{ℓ₂}{A}{B} f = ∀ (x y : A) → (f x ＝ f y) → (x ＝ y)

-- weaker
injective' : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set (ℓ ⊔ ℓ₁)
injective' {ℓ₁}{ℓ₂}{A}{B} f = ∀ (x y : A) → (x ≠ y) → (f x ≠ f y)

injective-injective' : {A : Set ℓ} {B : Set ℓ₂} → (f : A → B)
                     → injective f → injective' f
injective-injective' f p x y x≠y fx＝fy = x≠y (p x y fx＝fy)

{-
  mono and epi up to homotopy
-}

wmon : {A : Set ℓ} {B : Set ℓ₁} (f : A → B) → Set (lsuc (ℓ ⊔ ℓ₁))
wmon {ℓ}{ℓ₁}{A}{B} f = ∀{C : Set (ℓ ⊔ ℓ₁)} → (g h : C → A)
                       → (f ∘ g) ~ (f ∘ h) → g ~ h

wepi : {A : Set ℓ} {B : Set ℓ₁} (f : A → B) → Set (lsuc (ℓ ⊔ ℓ₁))
wepi {ℓ}{ℓ₁}{A}{B} f = ∀{C : Set (ℓ ⊔ ℓ₁)} → (g h : B → C)
                       → (g ∘ f) ~ (h ∘ f) → g ~ h

{-
  retracts, also split mono and epi
-}

-- r ∘ s ＝ id , embedding then quotient , s ; r ＝ id
has-retraction : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
has-retraction {ℓ}{ℓ₁} {X}{Y} s = Σ r ∶ (Y → X) , r ∘ s ~ id

-- right inverse
has-section : {X : Set ℓ} {Y : Set ℓ₁} → (Y → X) → Set (ℓ ⊔ ℓ₁)
has-section {ℓ}{ℓ₁} {X}{Y} r = Σ s ∶ (X → Y) , r ∘ s ~ id

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

invertible : {A : Set ℓ} {B : Set ℓ₁} (f : A → B) → Set (ℓ ⊔ ℓ₁)
invertible {ℓ}{ℓ₁} {A}{B} f = Σ g ∶ (B → A) , g ∘ f ~ id × f ∘ g ~ id

id-invertible : {X : Set ℓ} → invertible (id {ℓ}{X})
id-invertible {ℓ}{X} = id , refl , refl

inverse-invertible : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y}
                   → ((g , _) : invertible f) → invertible g
inverse-invertible {ℓ}{ℓ₁} {X}{Y} {f} (g , fg , gf) = f , gf , fg

invertible-∘ : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂} {f : X → Y} {f' : Y → Z}
             → invertible f' → invertible f → invertible (f' ∘ f)
-- middle terms cancel
invertible-∘ {ℓ}{ℓ₁}{ℓ₂} {X}{Y}{Z} {f}{f'} (g' , gf' , fg') (g , gf , fg) =
  g ∘ g' , (λ x → ap g (gf' (f x)) ∙ gf x) , λ z → ap f' (fg (g' z)) ∙ fg' z

{-
  theorems
-}

surj-comp : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
          → (f : A → B) → surjective f
          → (g : B → C) → surjective g
          → surjective (g ∘ f)
surj-comp {ℓ₁}{ℓ₂}{ℓ₃} {A}{B}{C} f pf g pg c
  = fiber-base pa , (ap g (fiber-id pa) ∙ fiber-id pb)
  where
    pb : fiber g c
    pb = pg c

    pa : fiber f (pr₁ pb)
    pa = pf (fiber-base pb)

surj-inj : {A : Set ℓ₁} {B : Set ℓ₂} → (f : A → B)
         → surjective f → Σ g ∶ (B → A) , injective g
surj-inj {ℓ₁}{ℓ₂} {A}{B} f surj
  = inj , λ x y p → sym＝ (fiber-id (surj x)) ∙ ap f p ∙ fiber-id (surj y)
  where
    inj : B → A
    inj b = fiber-base (surj b)

surj-inj-retract : {A : Set ℓ₁} {B : Set ℓ₂} → (f : A → B)
                 → (p : surjective f) → f ∘ pr₁ (surj-inj f p) ~ id
surj-inj-retract f p b = Σ.p2 (p b)

-- injection is weaker
inj-comp : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
         → (f : A → B) → injective f
         → (g : B → C) → injective g
         → injective (g ∘ f)
inj-comp f pf g pg = λ x y z → pf x y (pg (f x) (f y) z)

{-
  extensional
-}

ext-surjective : {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} → (f : A → (B → C))
               → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
ext-surjective {ℓ}{ℓ₁}{ℓ₂} {A}{B}{C} f = ∀ (g : B → C) → Σ a ∶ A , f a ~ g

surj-ext-surj : {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} → (f : A → (B → C))
              → surjective f → ext-surjective f
surj-ext-surj f p x = Σ.p1 (p x) , id~ (Σ.p2 (p x))

has-ext-section : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂}
                → (Z → (X → Y)) → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
has-ext-section {ℓ}{ℓ₁}{ℓ₂} {X}{Y}{Z} r
  = Σ s ∶ ((X → Y) → Z) , ∀ f → (r (s f)) ~ f

ext-retraction-surj : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
                    → (r : A → (B → C)) → has-ext-section r
                    → ext-surjective r
ext-retraction-surj r (s , p) = λ f → (s f , p f)
