{-# OPTIONS --without-K --exact-split --safe #-}

{-
  equivalence
-}

open import Agda.Primitive
open import logic
open import path
open import homotopy
open import hlevel
open import retract
open import retract-ex using (transport-is-section;Σ-retract)

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
is-equivalence : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
is-equivalence {ℓ}{ℓ₁} {X}{Y} f = Π y ∶ Y , is-contr (fiber f y)

-- inverses - center is p , Σ x, f x ＝ y
inverse : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) → is-equivalence f → (Y → X)
inverse f equivalence y = fiber-base (center (fiber f y) (equivalence y))

equiv-id : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} → (e : is-equivalence f)
         → (y : Y) → f (fiber-base (center _ (e y))) ＝ y
equiv-id equivalence y = fiber-id (center _ (equivalence y))

id-is-equivalence : (X : Set ℓ) → is-equivalence id
id-is-equivalence = singleton-types-are-singletons

-- comp-is-equivalence : {X : Set ℓ}{Y : Set ℓ₁}{Z : Set ℓ₂} {f : X → Y} {g : Y → Z}
--               → is-equivalence f → is-equivalence g → is-equivalence (g ∘ f)
-- comp-is-equivalence {ℓ}{ℓ₁}{ℓ₂} {X}{Y}{Z} {f} {g} ef eg z
--   = (fiber-base (center _ (ef (fiber-base (center _ (eg z))))) , test) , proof
--   where
--     test : g (f (inverse f ef (inverse g eg z))) ＝ z
--     test = ap g (equiv-id ef (inverse g eg z)) ∙ equiv-id eg z
--     -- not obvious!! we don't know anything about base or the space
--     proof : is-center (fiber (g ∘ f) z) ((inverse f ef (inverse g eg z)), test)
--     proof (base , gfbase＝z) = {!!}

{-
  relationship with invertibles
-}

-- the easy direction


inverses-are-sections : {X : Set ℓ} {Y : Set ℓ₁}
                      → (f : X → Y) (e : is-equivalence f)
                      → f ∘ inverse f e ~ id
inverses-are-sections f e y = fiber-id (center (fiber f y) (e y))

equiv-is-section : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                 → is-equivalence f → has-section f
equiv-is-section f e = inverse f e , inverses-are-sections f e

inverse-centrality : {X : Set ℓ} {Y : Set ℓ₁}
                     (f : X → Y) (e : is-equivalence f) (y : Y) (t : fiber f y)
                   → (inverse f e y , inverses-are-sections f e y) ＝ t
inverse-centrality f e y = centrality (fiber f y) (e y)

inverses-are-retractions : {X : Set ℓ} {Y : Set ℓ₁}
                           (f : X → Y) (e : is-equivalence f)
                         → inverse f e ∘ f ~ id
inverses-are-retractions f e x = ap pr₁ r
  where
    q : ∀ fb → (center _ (e (f x))) ＝ fb
    q = centrality _ (e (f x))
    -- inverse is just the base of the single fiber
    r : center (fiber f (f x)) (e (f x)) ＝ (x , refl (f x))
    r = q (x , refl (f x))

equiv-is-retraction : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                    → is-equivalence f → has-retraction f
equiv-is-retraction f e = inverse f e , inverses-are-retractions f e

equivalences-are-invertible : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                            → is-equivalence f → invertible f
equivalences-are-invertible f e = inverse f e ,
                                  inverses-are-retractions f e ,
                                  inverses-are-sections f e

-- the hard direction
invertibles-are-equivalences : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                             → invertible f → is-equivalence f
invertibles-are-equivalences {ℓ}{ℓ₁} {X}{Y} f (g , gf , fg) y₀ = proof
  where
    -- to show (Σ x ∶ X , f x ＝ y₀) ◁ (Σ x ∶ X , g (f x) ＝ g y₀)
    test : (x : X) → (f x ＝ y₀) ◁ (g (f x) ＝ g y₀)
    test x = rap g (f , fg) , ap g , rap-ap (f , fg)

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
inverse-is-equivalence : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} (e : is-equivalence f)
                       → is-equivalence (inverse f e)
inverse-is-equivalence {ℓ}{ℓ₁}{X}{Y} {f} e
  = invertibles-are-equivalences (inverse f e)
      (f , inverses-are-sections f e , inverses-are-retractions f e)

abstract
  equivalence-∘ : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂} {f : X → Y} {g : Y → Z}
                → is-equivalence g → is-equivalence f → is-equivalence (g ∘ f)
  equivalence-∘ {ℓ}{ℓ₁}{ℓ₂} {X}{Y}{Z} {f} {g} i j
    = invertibles-are-equivalences (g ∘ f)
        (invertible-∘ (equivalences-are-invertible g i)
                      (equivalences-are-invertible f j))

inverse-of-∘ : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂} (f : X → Y) (g : Y → Z)
             → (i : is-equivalence f) (j : is-equivalence g)
             → inverse f i ∘ inverse g j ~ inverse (g ∘ f) (equivalence-∘ j i)
inverse-of-∘ f g i j z = sym＝ (test2 (inverse f i (inverse g j z)))
                       ∙ ap (inverse (g ∘ f) (equivalence-∘ j i)) test
  where
    test : g (f (inverse f i (inverse g j z))) ＝ z
    test = ap g (equiv-id i (inverse g j z)) ∙ equiv-id j z

    test2 : inverse (g ∘ f) (equivalence-∘ j i) ∘ (g ∘ f) ~ id
    test2 = inverses-are-retractions (g ∘ f) (equivalence-∘ j i)

{-
  equivalent type-spaces
-}

_≃_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
X ≃ Y = Σ f ∶ (X → Y) , is-equivalence f
infix 5 _≃_

refl≃ : (X : Set ℓ) → X ≃ X
refl≃ X = id , id-is-equivalence X

sym≃ : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → Y ≃ X
sym≃ (f , e) = inverse f e , inverse-is-equivalence e

_●_ : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂} → X ≃ Y → Y ≃ Z → X ≃ Z
(f , d) ● (f' , e) = f' ∘ f , equivalence-∘ e d
trans≃ = _●_

_≃⟨_⟩_ : (X : Set ℓ) {Y : Set ℓ₁} {Z : Set ℓ₂} → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e
infixr 2 _≃⟨_⟩_

_■ : (X : Set ℓ) → X ≃ X
_■ = refl≃
infix 3 _■

invertible≃ : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) → invertible f → X ≃ Y
invertible≃ f i = f , invertibles-are-equivalences f i

◁≃ : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → X ◁ Y
◁≃ (f , e) = inverse f e , f , inverses-are-retractions f e

≃▷ : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → Y ◁ X
≃▷ (f , e) = f , inverse f e , inverses-are-sections f e

equivt-singletons : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y
                  → is-contr Y → is-contr X
equivt-singletons et = retract-of-singleton (◁≃ et)

equivt-subsingletons : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y
                     → is-subsingleton Y → is-subsingleton X
equivt-subsingletons et ssy = retract-of-subsingleton (◁≃ et) ssy

{-
  quasi-equivalence
-}

quasi-equivt : (A : Set ℓ) (B : Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
quasi-equivt A B = Σ f ∶ (A → B) , invertible f

quasi≃ : {A : Set ℓ} {B : Set ℓ₁} → (quasi-equivt A B) → A ≃ B
quasi≃ (f , if) = invertible≃ f if

equivt-quasi : {A : Set ℓ} {B : Set ℓ₁} → A ≃ B → (quasi-equivt A B)
equivt-quasi (f , ef) = f , equivalences-are-invertible f ef
