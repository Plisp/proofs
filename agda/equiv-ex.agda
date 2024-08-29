{-# OPTIONS --without-K --exact-split --safe #-}

{-
  examples
-}

open import Agda.Primitive
open import logic
open import path
open import homotopy
open import functor
open import retract
open import equiv

transport-is-equiv : {X : Set ℓ} (A : X → Set ℓ₁) {x y : X} (p : x ＝ y)
                   → is-equivalence (transport A p)
transport-is-equiv A p = invertibles-are-equivalences (transport A p)
                           (transport A (sym＝ p) ,
                           transport-is-section A p , transport-is-retraction A p)

bool-𝟚-equivt : Bool ≃ 𝟚
bool-𝟚-equivt = quasi≃ (bool-to-𝟚 , 𝟚-to-bool ,
                        (λ { true → refl true ; false → refl false}) ,
                        (λ { (inl ⋆) → refl _ ; (inr ⋆) → refl _ }))
  where
    bool-to-𝟚 : Bool → 𝟚
    bool-to-𝟚 true  = inl ⋆
    bool-to-𝟚 false = inr ⋆

    𝟚-to-bool : 𝟚 → Bool
    𝟚-to-bool (inl _) = true
    𝟚-to-bool (inr _) = false

{-
  products
-}

×＝-≃ : {X : Set ℓ} {Y : Set ℓ₁} (z t : X × Y)
      → (z ＝ t) ≃ ((fst z ＝ fst t) × (snd z ＝ snd t))
×＝-≃ {ℓ} {ℓ₁} {X} {Y} z@(z1 , z2) t@(t1 , t2) = invertible≃ from-×＝ (to-×＝ , η , ε)
 where
  η : (p : z ＝ t) → to-×＝ (from-×＝ p) ＝ p
  η (refl (a , b)) = refl (refl (a , b))

  ε : (q : (fst z ＝ fst t) × (snd z ＝ snd t)) → from-×＝ (to-×＝ q) ＝ q
  ε (refl x , refl y) = refl (refl x , refl y)

×-cong : {W : Set ℓ} {X : Set ℓ₁} {Y : Set ℓ₂} {Z : Set ℓ₃}
       → W ≃ Y → X ≃ Z
       → (W × X) ≃ (Y × Z)
×-cong {ℓ}{ℓ₁}{ℓ₂}{ℓ₃} {W}{X}{Y}{Z} (f , ef) (g , eg)
  = quasi≃ (f× f g , f× (Σ.p1 fi) (Σ.p1 gi) ,
            (λ {(a , b) → to-×＝ (fst (Σ.p2 fi) a , fst (Σ.p2 gi) b)}) ,
            (λ {(a , b) → to-×＝ (snd (Σ.p2 fi) a , snd (Σ.p2 gi) b)}))
  where
    fi = equivalences-are-invertible f ef
    gi = equivalences-are-invertible g eg

{-
  sums
-}

＋-cong : {W : Set ℓ} {X : Set ℓ₁} {Y : Set ℓ₂} {Z : Set ℓ₃}
       → W ≃ Y → X ≃ Z
       → (W ＋ X) ≃ (Y ＋ Z)
＋-cong {ℓ}{ℓ₁}{ℓ₂}{ℓ₃} {W}{X}{Y}{Z} (f , ef) (g , eg)
  = quasi≃ (f＋ f g , f＋ (Σ.p1 fi) (Σ.p1 gi) ,
            (λ {(inl a) → ap inl (fst (Σ.p2 fi) a) ;
                (inr b) → ap inr (fst (Σ.p2 gi) b)}) ,
            (λ {(inl a) → ap inl (snd (Σ.p2 fi) a) ;
                (inr b) → ap inr (snd (Σ.p2 gi) b)}))
  where
    fi = equivalences-are-invertible f ef
    gi = equivalences-are-invertible g eg

{-
  sigma types
-}

Σ-induction-≃ : {X : Set ℓ} {Y : X → Set ℓ₁} {A : Σ Y → Set ℓ₂}
              → ((x : X) (y : Y x) → A (x , y)) ≃ ((z : Σ Y) → A z)
Σ-induction-≃ = invertible≃ (λ z (x , y) → z x y)
                  ((λ z x y → z (x , y)) , refl , refl)

Σ-sym : {X : Set ℓ} {Y : Set ℓ₁} {A : X → Y → Set ℓ₂}
      → (Σ x ∶ X , Σ y ∶ Y , A x y) ≃ (Σ y ∶ Y , Σ x ∶ X , A x y)
Σ-sym = invertible≃ (λ (x , y , p) → (y , x , p))
          ((λ (y , x , p) → (x , y , p)) , refl , refl)

Σ-assoc : {X : Set ℓ} {Y : X → Set ℓ₁} {Z : Σ Y → Set ℓ₂}
        → Σ Z ≃ (Σ x ∶ X , Σ y ∶ Y x , Z (x , y))
Σ-assoc = invertible≃ (λ { ((x , y) , z) → x , y , z })
                      ((λ { (x , y , z) → (x , y) , z }) , refl , refl)

Σ＝-≃ : {X : Set ℓ} {A : X → Set ℓ₁} (σ τ : Σ A)
      → (σ ＝ τ) ≃ (Σ p ∶ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
Σ＝-≃ {ℓ} {ℓ₁} {X} {A} σ τ = invertible≃ from-Σ＝ (to-Σ＝ , η , ϵ)
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
    f x = Σ.p1 (φ x)

    g : (x : X) → B x → A x
    g x = inverse (f x) (Σ.p2 (φ x))

    η : (x : X) (a : A x) → g x (f x a) ＝ a
    η x = inverses-are-retractions _ (Σ.p2 (φ x))

    ϵ : (x : X) (b : B x) → f x (g x b) ＝ b
    ϵ x = inverses-are-sections _ (Σ.p2 (φ x))

    η＝ : NatΣ g ∘ NatΣ f ~ id
    η＝ (x , ax) = to-Σ＝ (refl _ , η x ax)

    ϵ＝ : NatΣ f ∘ NatΣ g ~ id
    ϵ＝ (x , bx) = to-Σ＝ (refl _ , ϵ x bx)
