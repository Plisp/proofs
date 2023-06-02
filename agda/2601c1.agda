{-# OPTIONS --without-K --exact-split --safe #-}
open import Agda.Primitive
open import logic
open import eq
open import op

Group : (ℓ : Level) → Set (lsuc ℓ)
Group ℓ = Σ X ꞉ (Set ℓ) ,
          (Σ _·_ ꞉ (X → X → X) ,
            ((op-assoc _·_) ×
             (Σ e ꞉ X ,
               ((op-id e _·_) × (op-inverse e _·_)))))

AbelianGroup : (ℓ : Level) → Set (lsuc ℓ)
AbelianGroup ℓ = Σ X ꞉ (Set ℓ) ,
                 (Σ _·_ ꞉ (X → X → X) ,
                   (((op-commut _·_) × (op-assoc _·_)) ×
                   (Σ e ꞉ X ,
                     ((op-id e _·_) × (op-inverse e _·_)))))


⟨_⟩ : Group ℓ → Set ℓ
⟨ X , _ ⟩ = X

group-op : (G : Group ℓ) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
group-op (X , (· , _)) = ·
