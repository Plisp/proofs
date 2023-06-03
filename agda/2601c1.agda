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
syntax group-op G x y = x ·⟨ G ⟩ y

group-id : (G : Group ℓ) → ⟨ G ⟩
group-id (X , (· , (_ , (e , _)))) = e

is-inverse : (G : Group ℓ) → ⟨ G ⟩ → ⟨ G ⟩ → Set ℓ
is-inverse G x y = (x ·⟨ G ⟩ y ＝ (group-id G)) × (y ·⟨ G ⟩ x ＝ (group-id G))

inverse : (G : Group ℓ) → ⟨ G ⟩ → ⟨ G ⟩
inverse (X , (· , (_ , (_ , (_ , invp))))) x = pr₁ (invp x)

-- lemma 1.1
-- e' = e'·e ＝ e
unique-id : (G : Group ℓ)
          → (e' : ⟨ G ⟩)
          → (op-id e' (group-op G))
          → e' ＝ (group-id G)
unique-id -- mfw no record sugar
  (X , (· , (_ , (e , (idp , _))))) e' f
  = sym (fst (idp e')) ∙ snd (f e)

-- x' · x · y (= e · y = y) (= x' · e = x')
unique-inv : (G : Group ℓ)
           → (x : ⟨ G ⟩)
           → (x' : ⟨ G ⟩)
           → is-inverse G x x'
           → x' ＝ inverse G x
unique-inv G x x' p = let y = inverse G x in {!!}

inv-olution : (G : Group ℓ)
            → (x : ⟨ G ⟩)
            → x ＝ (inverse G (inverse G x))
inv-olution G x = unique-inv G (inverse G x) x {!!}

-- TODO
-- (a·b)⁻¹ = b⁻¹·a⁻¹ multiply by a.b and prove is-inverse
-- (a·b) = (a·c) → b = c, multiply by inverse a, cancel
-- (b·a) = (c·a) → b = c









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
