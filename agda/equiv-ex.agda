{-# OPTIONS --without-K --exact-split --safe #-}

{-
  examples
-}

open import Agda.Primitive
open import logic
open import path
open import homotopy
open import hlevel
open import retract
open import retract-ex
open import equiv

quasi-equiv : (A : Set ℓ) (B : Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
quasi-equiv A B = Σ f ∶ (A → B) , invertible f

transport-is-equiv : {X : Set ℓ} (A : X → Set ℓ₁) {x y : X} (p : x ＝ y)
                   → is-equivalence (transport A p)
transport-is-equiv A p = invertibles-are-equivalences (transport A p)
                           (transport A (sym＝ p) ,
                           transport-is-section A p , transport-is-retraction A p)

{-
  products
-}

×-＝-≃ : {X : Set ℓ} {Y : Set ℓ₁} (z t : X × Y)
      → (z ＝ t) ≃ ((fst z ＝ fst t) × (snd z ＝ snd t))
×-＝-≃ {ℓ} {ℓ₁} {X} {Y} z@(z1 , z2) t@(t1 , t2) = invertible≃ from-×＝ (to-×＝ , η , ε)
 where
  η : (p : z ＝ t) → to-×＝ (from-×＝ p) ＝ p
  η (refl (a , b)) = refl (refl (a , b))

  ε : (q : (fst z ＝ fst t) × (snd z ＝ snd t)) → from-×＝ (to-×＝ q) ＝ q
  ε (refl x , refl y) = refl (refl x , refl y)

{-
  sigma types
-}

Σ-induction-≃ : {X : Set ℓ} {Y : X → Set ℓ₁} {A : Σ Y → Set ℓ₂}
              → ((x : X) (y : Y x) → A (x , y)) ≃ ((z : Σ Y) → A z)
Σ-induction-≃ = invertible≃ (λ z (x , y) → z x y)
                  ((λ z x y → z (x , y)) , refl , refl)

Σ-flip : {X : Set ℓ} {Y : Set ℓ₁} {A : X → Y → Set ℓ₂}
       → (Σ x ∶ X , Σ y ∶ Y , A x y) ≃ (Σ y ∶ Y , Σ x ∶ X , A x y)
Σ-flip = invertible≃ (λ (x , y , p) → (y , x , p))
           ((λ (y , x , p) → (x , y , p)) , refl , refl)

Σ-＝-≃ : {X : Set ℓ} {A : X → Set ℓ₁} (σ τ : Σ A)
      → (σ ＝ τ) ≃ (Σ p ∶ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
Σ-＝-≃ {ℓ} {ℓ₁} {X} {A} σ τ = invertible≃ from-Σ＝ (to-Σ＝ , η , ϵ)
  where
    η : (q : σ ＝ τ) → to-Σ＝ (from-Σ＝ q) ＝ q
    η (refl σ) = refl _

    ϵ : (w : Σ p ∶ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
      → from-Σ＝ (to-Σ＝ w) ＝ w
    ϵ (refl p , refl q) = refl _

Σ-cong : {X : Set ℓ} {A : X → Set ℓ₁} {B : X → Set ℓ₂}
       → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B
Σ-cong {ℓ} {ℓ₁} {ℓ₂} {X} {A} {B} φ = invertible≃ (NatΣ f) (NatΣ g , η＝ , ϵ＝)
  where
    f : (x : X) → A x → B x
    f x = equivt-fn (φ x)

    g : (x : X) → B x → A x
    g x = inverse (f x) (is-equivt (φ x))

    η : (x : X) (a : A x) → g x (f x a) ＝ a
    η x = inverses-are-retractions _ (is-equivt (φ x))

    ϵ : (x : X) (b : B x) → f x (g x b) ＝ b
    ϵ x = inverses-are-sections _ (is-equivt (φ x))

    η＝ : NatΣ g ∘ NatΣ f ~ id
    η＝ (x , ax) = to-Σ＝ (refl _ , η x ax)

    ϵ＝ : NatΣ f ∘ NatΣ g ~ id
    ϵ＝ (x , bx) = to-Σ＝ (refl _ , ϵ x bx)

-- TODO joyal stuff
