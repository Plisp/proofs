{-# OPTIONS --without-K --exact-split --safe #-}

{-
  univalence definitions
-}

open import Agda.Primitive
open import logic
open import types
open import path
open import hlevel
open import retract

{-
  Voevodsky's equivalence
-}

-- space: witnesses x' × f x' = y
fiber : {X :  Set ℓ} {Y : Set ℓ₁} (f : X → Y) → Y → Set (ℓ ⊔ ℓ₁)
fiber {ℓ}{ℓ₁} {X}{Y} f y = Σ x ∶ X , f x ＝ y

fiber-base : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
           → fiber f y → X
fiber-base (x , p) = x

fiber-id : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
         → (w : fiber f y) → f (fiber-base w) ＝ y
fiber-id (x , p) = p

-- the fibre (preimage) of all y : Y under f is unique (size 1)
-- the proof is also unique, via the characterisation of Σ identity
is-equiv : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
is-equiv {ℓ}{ℓ₁} {X}{Y} f = Π y ∶ Y , is-contr (fiber f y)

_≃_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
X ≃ Y = Σ f ∶ (X → Y) , is-equiv f
infix 5 _≃_

equiv-fn : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → X → Y
equiv-fn (f , i) = f

id-is-equiv : (X : Set ℓ) → is-equiv id
id-is-equiv = singleton-types-are-singletons

refl≃ : (X : Set ℓ) → X ≃ X
refl≃ X = id , id-is-equiv X

-- inverses - center is p , Σ x, f x ＝ y
inverse : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) → is-equiv f → (Y → X)
inverse f equiv y = fiber-base (center (fiber f y) (equiv y))

{-
  relationship with invertibles
-}

invertible : {A : Set ℓ} {B : Set ℓ₁} (f : A → B) → Set (ℓ ⊔ ℓ₁)
invertible {ℓ}{ℓ₁} {A}{B} f = Σ g ∶ (B → A) , g ∘ f ~ id × f ∘ g ~ id

-- the easy direction
inverses-are-sections : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) (e : is-equiv f)
                      → f ∘ inverse f e ~ id
inverses-are-sections f e y = fiber-id (center (fiber f y) (e y))

inverse-centrality : {X : Set ℓ} {Y : Set ℓ₁}
                     (f : X → Y) (e : is-equiv f) (y : Y) (t : fiber f y)
                   → (inverse f e y , inverses-are-sections f e y) ＝ t
inverse-centrality f e y = centrality (fiber f y) (e y)

inverses-are-retractions : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) (e : is-equiv f)
                         → inverse f e ∘ f ~ id
inverses-are-retractions f e x = ap pr₁ r
  where
    q : ∀ fb → (center _ (e (f x))) ＝ fb
    q = centrality _ (e (f x))
    -- inverse is just the base of the single fiber
    r : center (fiber f (f x)) (e (f x)) ＝ (x , refl (f x))
    r = q (x , refl (f x))

equivs-are-invertible : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                      → is-equiv f → invertible f
equivs-are-invertible f e = inverse f e ,
                            inverses-are-retractions f e ,
                            inverses-are-sections f e

-- the hard direction
rap : {X : Set ℓ} {Y : Set ℓ₁} {x y : X} (f : X → Y)
    → has-retraction f → (f x ＝ f y) → (x ＝ y)
rap {ℓ}{ℓ₁}{X}{Y} {x}{y} f (g , gf) p = sym＝ (gf x) ∙ (ap g p) ∙ gf y

ap-rap : {X : Set ℓ} {Y : Set ℓ₁} {x y : X}
       → (f : X → Y) (r : has-retraction f)
       → (p : x ＝ y) → rap f r (ap f p) ＝ p
ap-rap {ℓ}{ℓ₁}{X}{Y} {x}{y} f (g , gf) (refl x)
  = ap (λ e → sym＝ (gf x) ∙ e) (sym＝ (p＝refl∙p (gf x))) ∙ iv∙p＝refl _

invertibles-are-equivs : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                       → invertible f → is-equiv f
invertibles-are-equivs {ℓ}{ℓ₁} {X}{Y} f (g , gf , fg) y₀ = proof
  where
    -- to show (Σ x ∶ X , f x ＝ y₀) ◁ (Σ x ∶ X , g (f x) ＝ g y₀)
    test : (x : X) → (f x ＝ y₀) ◁ (g (f x) ＝ g y₀)
    test x = rap g (f , fg) , ap g , ap-rap g (f , fg)

    hom-iso : ∀ x → (g (f x) ＝ g y₀) ◁ (x ＝ g y₀)
    hom-iso x = transport (λ - → - ＝ g y₀) (sym＝ (gf x)) ,
                transport (_＝ g y₀) (gf x) ,
                transport-is-section (_＝ g y₀) (gf x)

    -- want to show the fiber type is a retract of a singleton(-type)
    fiber-is-singleton-Σ-retract : (fiber f y₀) ◁ (Σ x ∶ X , x ＝ g y₀)
    fiber-is-singleton-Σ-retract
      = (Σ x ∶ X , f x ＝ y₀)       ◁⟨ Σ-retract test ⟩
        (Σ x ∶ X , g (f x) ＝ g y₀) ◁⟨ Σ-retract hom-iso ⟩
        (Σ x ∶ X , x ＝ g y₀)       ◀ -- these are just ∙ (sym＝) gf which cancel

    proof : Σ c ∶ (fiber f y₀) , is-center _ c
    proof = retract-of-singleton fiber-is-singleton-Σ-retract
              (singleton-types-are-singletons _ (g y₀))


-- corollaries
-- inverses-are-equivs : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) (e : is-equiv f)
--                     → is-equiv (inverse f e)
-- inverses-are-equivs = {!!}

{-
  univalence
-}

quasi-equiv : (A : Set ℓ) (B : Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
quasi-equiv A B = Σ f ∶ (A → B) , invertible f

Id→Eq : (X Y : Set ℓ) → X ＝ Y → X ≃ Y
Id→Eq X X (refl X) = refl≃ X

is-univalent : (ℓ : Level) → Set (lsuc ℓ)
is-univalent ℓ = ∀ (X Y : Set ℓ) → is-equiv (Id→Eq X Y)

univalence-≃ : is-univalent ℓ → (X Y : Set ℓ) → (X ＝ Y) ≃ (X ≃ Y)
univalence-≃ ua X Y = Id→Eq X Y , ua X Y

Eq→Id : is-univalent ℓ → (X Y : Set ℓ) → X ≃ Y → X ＝ Y
Eq→Id ua X Y = inverse (Id→Eq X Y) (ua X Y)

Id→fun : {X Y : Set ℓ} → X ＝ Y → X → Y
Id→fun {ℓ} {X} {Y} p = equiv-fn (Id→Eq X Y p)
