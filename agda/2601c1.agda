{-# OPTIONS --without-K --exact-split --safe #-}

{-
  2601 lemmas formalized
-}

open import Agda.Primitive
open import logic
open import paths
open import op

record Group (S : Set ℓ) : Set (lsuc ℓ) where
  constructor ⟨_,_,_,_,_⟩
  field
    op : S → S → S
    e : S
    assocp : assoc op
    idp : identity e op
    ivp : inverse e op

-- TODO how to best represent while reusing Group?
-- AbelianGroup : (ℓ : Level) → Set (lsuc ℓ)
-- AbelianGroup ℓ = Σ X ∶ (Set ℓ) ,
--                  Σ _·_ ∶ (X → X → X) ,
--                    (op-commut _·_) × (op-assoc _·_)
--                  × (Σ e ∶ X , (op-id e _·_) × (op-inverse e _·_))

-- hack? not sure why can't use record accessor
group-op = Group.op
syntax group-op G x y = x ·⟨ G ⟩ y

is-inverse : {S : Set ℓ} → (G : Group S) → S → S → Set ℓ
is-inverse ⟨ _·_ , e , _ , _ , _ ⟩ x y = (x · y ＝ e) × (y · x ＝ e)

get-inverse : {S : Set ℓ} → (G : Group S) → S → S
get-inverse G x = pr₁ (Group.ivp G x)

{-
  trivial group
-}

triv-op : 𝟙 → 𝟙 → 𝟙
triv-op _ _ = ⋆

triv-assoc : assoc triv-op -- ∀ a b c → (a·b)·c ＝ a·(b·c)
triv-assoc _ _ _ = refl ⋆

triv-id : identity ⋆ triv-op  -- ∀ x → (x·e ＝ x) × (e·x ＝ x)
triv-id ⋆ = (refl ⋆ , refl ⋆)

triv-inverse : inverse ⋆ triv-op -- ∀ x → Σ y꞉X, (x·y ＝ e) × (y·x ＝ e)
triv-inverse ⋆ = (⋆ , (refl ⋆ , refl ⋆))

triv-group : Group 𝟙
triv-group = ⟨ triv-op , ⋆ , triv-assoc , triv-id , triv-inverse ⟩

{-
  lemma 1.1
-}

unique-id : {S : Set ℓ} → (G : Group S)
          → (e' : S)
          → (identity e' (Group.op G))
          → e' ＝ (Group.e G)
-- e' = e'·e ＝ e
unique-id G e' f = sym＝ (fst (Group.idp G e')) ∙ snd (f (Group.e G))

unique-inv : {S : Set ℓ} → (G : Group S)
           → (x x' : S)
           → is-inverse G x x'
           → x' ＝ get-inverse G x
unique-inv G@(⟨ _·_ , e , assocp , idp , ivp ⟩) x x' p = sym＝ p1 ∙ p2
  where
    y = get-inverse G x

    p1 : (x' · x) · y ＝ x'
    p1 =
      begin                                          (x' · x) · y
        =⟨ assocp x' x y ⟩                            x' · (x · y)
        =⟨ ap (λ a → (x' · a)) (fst (pr₂ (ivp x))) ⟩ x' · e
        =⟨ fst (idp x') ⟩                            x'
      ∎

    p2 : (x' · x) · y ＝ y
    p2 =
      begin                             (x' · x) · y
        =⟨ ap (λ a → (a · y)) (snd p) ⟩ e · y
        =⟨ (snd (idp y)) ⟩              y

      ∎

inv-olution : {S : Set ℓ} → (G : Group S)
            → (x : S)
            → x ＝ (get-inverse G (get-inverse G x))
inv-olution G@(⟨ _·_ , e , assocp , idp , ivp ⟩) x
  = unique-inv G (get-inverse G x) x p
  where
    p : ((get-inverse G x) · x ＝ e) × (x · (get-inverse G x) ＝ e)
    p = (snd (pr₂ (ivp x))) , (fst (pr₂ (ivp x)))

-- (a·b) = (a·c) → b = c, multiply by get-inverse a
lcancel : {S : Set ℓ} → (G : Group S)
        → (a b c : S)
        → (a ·⟨ G ⟩ b) ＝ (a ·⟨ G ⟩ c)
        → b ＝ c
lcancel G@(⟨ _·_ , e , assocp , idp , ivp ⟩) a b c p
  = sym＝ (lemma2 b) ∙ lemma1 ∙ (lemma2 c)
  where
    a' = (get-inverse G a)

    lemma1 : (a' · a) · b ＝ (a' · a) · c
    lemma1 = (assocp a' a b) ∙ (ap (λ x → a' · x) p) ∙ sym＝ (assocp a' a c)

    lemma2 : ∀ d → (a' · a) · d ＝ d
    lemma2 d = (ap (λ x → x · d) (snd (pr₂ (ivp a)))) ∙ (snd (idp d))

rcancel : {S : Set ℓ} → (G : Group S)
        → (a b c : S)
        → (b ·⟨ G ⟩ a) ＝ (c ·⟨ G ⟩ a)
        → b ＝ c
rcancel G@(⟨ _·_ , e , assocp , idp , ivp ⟩) a b c p
  = (sym＝ (lemma2 b)) ∙ lemma1 ∙ (lemma2 c)
  where
    a' = (get-inverse G a)

    lemma1 : b · (a · a') ＝ c · (a · a')
    lemma1 = (sym＝ (assocp b a a')) ∙ (ap (λ x → x · a') p) ∙ (assocp c a a')

    lemma2 : ∀ d → d · (a · a') ＝ d
    lemma2 d = (ap (λ x → d · x) (fst (pr₂ (ivp a)))) ∙ (fst (idp d))

inv-comp : {S : Set ℓ} → (G : Group S)
         → (a b : S)
         → (get-inverse G (a ·⟨ G ⟩ b)) ＝ (get-inverse G b) ·⟨ G ⟩ (get-inverse G a)
inv-comp G@(⟨ _·_ , e , assocp , idp , ivp ⟩) a b
  = sym＝ (unique-inv G (a · b) ((get-inverse G b) · (get-inverse G a)) (p , q))
  where
    a' = (get-inverse G a)
    b' = (get-inverse G b)

    p : ((a · b) · (b' · a') ＝ e)
    p =
      begin                                              (a · b) · (b' · a')
        =⟨ sym＝ (assocp (a · b) b' a') ⟩                 ((a · b) · b') · a'
        =⟨ ap (λ x → x · a') (assocp a b b') ⟩           (a · (b · b')) · a'
        =⟨ ap (λ x → (a · x) · a') (fst (pr₂ (ivp b))) ⟩ (a · e) · a'
        =⟨ ap (λ x → x · a') (fst (idp a)) ⟩             a · a'
        =⟨ (fst (pr₂ (ivp a))) ⟩                         e
      ∎

    q : ((b' · a') · (a · b) ＝ e)
    q =
      begin                                              (b' · a') · (a · b)
        =⟨ sym＝ (assocp (b' · a') a b) ⟩                 ((b' · a') · a) · b
        =⟨ ap (λ x → x · b) (assocp b' a' a) ⟩           (b' · (a' · a)) · b
        =⟨ ap (λ x → (b' · x) · b) (snd (pr₂ (ivp a))) ⟩ (b' · e) · b
        =⟨ ap (λ x → x · b) (fst (idp b')) ⟩             b' · b
        =⟨ (snd (pr₂ (ivp b))) ⟩                         e
      ∎

{-
  bijections (functions with inverses)
-}

data Bij (S : Set ℓ) : Set ℓ where
  ♭ : (f : S → S) → (f' : S → S) → (f ∘ f' ＝ id) → (f' ∘ f ＝ id) → Bij S

-- bij-op : {S : Set ℓ} → Bij S → Bij S → Bij S
-- bij-op (♭ f f' fp fq) (♭ g g' gp gq) = ?

-- bij-id : {S : Set ℓ} → Bij S
-- bij-id = ?

-- bij-idp : {S : Set ℓ} → op-id{ℓ}{Bij S} bij-id bij-op
-- bij-idp{ℓ}{S} (♭ f f' p q) = ?

-- bij-ivp : {S : Set ℓ} → op-inverse{ℓ}{Bij S} bij-id bij-op
-- bij-ivp (♭ f f' p q) = ?

-- bij-assoc : {S : Set ℓ} → op-assoc{ℓ}{Bij S} bij-op
-- bij-assoc f g h = ?

-- bij-group : {S : Set ℓ} → Group (Bij S)
-- bij-group = ⟨ bij-op , bij-id , bij-assoc , bij-idp , bij-ivp ⟩

{- TODO
  modulo group ℤₙ = Fin n is homomorphic to cyclic field ℂₙ
-}

is-homo : {A : Set ℓ₁} {B : Set ℓ₂}
        → (GA : Group A) → (GB : Group B) → (A → B) → Set (ℓ₁ ⊔ ℓ₂)
is-homo GA GB f = ∀ a b → f (a ·⟨ GA ⟩ b) ＝ (f a) ·⟨ GB ⟩ (f b)

data Homomorphism (A : Set ℓ₁) (B : Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  H : {GA : Group A} → {GB : Group B}
    → (f : A → B)
    → (is-homo GA GB f) → Homomorphism A B
