{-# OPTIONS --without-K --exact-split --safe #-}

{-
  internal homotopy
-}

open import Agda.Primitive
open import logic
open import path

_~_ : {X : Set ℓ} {A : X → Set ℓ₁} → Π A → Π A → Set (ℓ ⊔ ℓ₁)
f ~ g = ∀ x → (f x ＝ g x)
infix 5 _~_

id~ : {A : Set ℓ} {P : A → Set ℓ₁} → {f g : Π x ∶ A , P x}
    → (f ＝ g) → (f ~ g)
id~ (refl f) = λ x → refl (f x)

-- equivalence relation
refl~ : {A : Set ℓ} {P : A → Set ℓ₁} → (f : Π x ∶ A , P x) → (f ~ f)
refl~ f = λ x → refl (f x)

sym~ : {A : Set ℓ} {P : A → Set ℓ₁} → {f g : Π x ∶ A , P x}
     → (f ~ g) → (g ~ f)
sym~ hom = λ x → sym＝ (hom x)

trans~ : {A : Set ℓ} {P : A → Set ℓ₁} → {f g h : Π x ∶ A , P x}
       → (f ~ g) → (g ~ h) → (f ~ h)
trans~ homf homg = λ x → trans＝ (homf x) (homg x)

-- naturality
nat~ : {A : Set ℓ} {B : Set ℓ₁}
     → (f g : A → B) (H : f ~ g) → {x y : A} (p : x ＝ y)
     → H x ∙ ap g p ＝ ap f p ∙ H y
nat~ f g H {x}{y} = ȷ (λ x y p → H x ∙ ap g p ＝ ap f p ∙ H y)
                      (λ x → p∙refl＝p (H x) ∙ p＝refl∙p (H x))
                      x y

commut~ : {A : Set ℓ} → (f : A → A) (H : f ~ id)
        → (x : A) → H (f x) ＝ ap f (H x)
commut~ f H x = simplify (nat~ f id H {f x} {x} (H x))
  where
    lemma1 : H (f x) ∙ (H x) ＝ H (f x) ∙ ap id (H x)
    lemma1 = ap (λ e → H (f x) ∙ e) (sym＝ (ap-id-p＝p (H x)))

    whisker : H (f x) ∙ (H x) ＝ ap f (H x) ∙ (H x)
            → H (f x) ∙ (H x) ∙ (sym＝ (H x)) ＝ ap f (H x) ∙ (H x) ∙ (sym＝ (H x))
    whisker p = sym＝ (assoc∙ (H (f x)) (H x) (sym＝ (H x)))
              ∙ ap (λ e → e ∙ sym＝ (H x)) p
              ∙ assoc∙ (ap f (H x)) (H x) (sym＝ (H x))

    lemma3 : H (f x) ＝ H (f x) ∙ (H x) ∙ (sym＝ (H x))
    lemma3 = sym＝ (p∙refl＝p (H (f x)))
           ∙ ap (λ e → H (f x) ∙ e) (sym＝ (p∙iv＝refl (H x)))

    lemma4 : ap f (H x) ∙ (H x) ∙ (sym＝ (H x)) ＝ ap f (H x)
    lemma4 = ap (λ e → ap f (H x) ∙ e) (p∙iv＝refl (H x)) ∙ (p∙refl＝p (ap f (H x)))

    simplify : H (f x) ∙ ap id (H x) ＝ ap f (H x) ∙ (H x) → _
    simplify p = lemma3 ∙ whisker (lemma1 ∙ p) ∙ lemma4
