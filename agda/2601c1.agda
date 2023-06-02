{-# OPTIONS --without-K --exact-split --safe #-}
open import Agda.Primitive
open import logic
open import eq
open import op

Group : (ℓ : Level) → Set (lsuc ℓ)
Group ℓ = Σ X ꞉ (Set ℓ) ,
          Σ _·_ ꞉ (X → X → X) ,
            (op-assoc _·_)
          × (Σ e ꞉ X , (op-id e _·_) × (op-inverse e _·_))

AbelianGroup : (ℓ : Level) → Set (lsuc ℓ)
AbelianGroup ℓ = Σ X ꞉ (Set ℓ) ,
                 Σ _·_ ꞉ (X → X → X) ,
                   (op-commut _·_) × (op-assoc _·_)
                 × (Σ e ꞉ X , (op-id e _·_) × (op-inverse e _·_))

⟨_⟩ : Group ℓ → Set ℓ
⟨ X , _ ⟩ = X

group-op : (G : Group ℓ) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
group-op (X , (· , _)) = ·

-- trivial group
triv-op : 𝟙 → 𝟙 → 𝟙
triv-op _ _ = ⋆

triv-assoc : op-assoc triv-op -- ∀ a b c → (a·b)·c ＝ a·(b·c)
triv-assoc _ _ _ = refl ⋆

triv-id : op-id ⋆ triv-op  -- ∀ x → (x·e ＝ x) × (e·x ＝ x)
triv-id ⋆ = (refl ⋆ , refl ⋆)

triv-inverse : op-inverse ⋆ triv-op -- ∀x → Σ y꞉X, (x·y ＝ e) × (y·x ＝ e)
triv-inverse ⋆ = (⋆ , (refl ⋆ , refl ⋆))

triv-group : Group lzero
triv-group = (𝟙 ,
             (triv-op , (triv-assoc , (⋆ , (triv-id , triv-inverse)))))
