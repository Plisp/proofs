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

surjective :{A : Set ℓ₁} {B : Set ℓ₂} → (f : A → B) → Set (ℓ₁ ⊔ ℓ₂)
surjective {ℓ₁}{ℓ₂} {A}{B} f = ∀ (y : B) → fiber f y

injective : {A : Set ℓ₁} {B : Set ℓ₂} → (f : A → B) → Set (ℓ₁ ⊔ ℓ₂)
injective {ℓ₁}{ℓ₂}{A}{B} f = ∀ (x y : A) → (f x ＝ f y) → (x ＝ y)

injective' : {A : Set ℓ₁} {B : Set ℓ₂} → (f : A → B) → Set (ℓ₁ ⊔ ℓ₂)
injective' {ℓ₁}{ℓ₂}{A}{B} f = ∀ (x y : A) → (x ≠ y) → (f x ≠ f y)

injective-injective' : {A : Set ℓ₁} {B : Set ℓ₂} → (f : A → B)
                     → injective f → injective' f
injective-injective' f p x y x≠y fx＝fy = x≠y (p x y fx＝fy)

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
