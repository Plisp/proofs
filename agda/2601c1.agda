{-# OPTIONS --without-K --exact-split --safe #-}

{-
  2601 lemmas formalized
-}

open import Agda.Primitive
open import logic
open import eq
open import op

record Group {ℓ : Level} (S : Set ℓ) : Set (lsuc ℓ) where
  constructor ⟨_,_,_,_,_⟩
  field
    op : S → S → S
    e : S
    assoc : op-assoc op
    idp : op-id e op
    ivp : op-inverse e op

-- AbelianGroup : (ℓ : Level) → Set (lsuc ℓ)
-- AbelianGroup ℓ = Σ X ꞉ (Set ℓ) ,
--                  Σ _·_ ꞉ (X → X → X) ,
--                    (op-commut _·_) × (op-assoc _·_)
--                  × (Σ e ꞉ X , (op-id e _·_) × (op-inverse e _·_))

-- hack? not sure why can't use record accessor
group-op = Group.op
syntax group-op G x y = x ·⟨ G ⟩ y

is-inverse : {S : Set ℓ} → (G : Group S) → S → S → Set ℓ
is-inverse ⟨ _·_ , e , _ , _ , _ ⟩ x y = (x · y ＝ e) × (y · x ＝ e)

inverse : {S : Set ℓ} → (G : Group S) → S → S
inverse G x = pr₁ (Group.ivp G x)

{-
  trivial group
-}

triv-op : 𝟙 → 𝟙 → 𝟙
triv-op _ _ = ⋆

triv-assoc : op-assoc triv-op -- ∀ a b c → (a·b)·c ＝ a·(b·c)
triv-assoc _ _ _ = refl ⋆

triv-id : op-id ⋆ triv-op  -- ∀ x → (x·e ＝ x) × (e·x ＝ x)
triv-id ⋆ = (refl ⋆ , refl ⋆)

triv-inverse : op-inverse ⋆ triv-op -- ∀x → Σ y꞉X, (x·y ＝ e) × (y·x ＝ e)
triv-inverse ⋆ = (⋆ , (refl ⋆ , refl ⋆))

triv-group : Group 𝟙
triv-group = ⟨ triv-op , ⋆ , triv-assoc , triv-id , triv-inverse ⟩

{-
  lemma 1.1
-}

unique-id : {S : Set ℓ} → (G : Group S)
          → (e' : S)
          → (op-id e' (Group.op G))
          → e' ＝ (Group.e G)
-- e' = e'·e ＝ e
unique-id G e' f = sym (fst (Group.idp G e')) ∙ snd (f (Group.e G))

unique-inv : {S : Set ℓ} → (G : Group S)
           → (x x' : S)
           → is-inverse G x x'
           → x' ＝ inverse G x
unique-inv G@(⟨ _·_ , e , assoc , idp , ivp ⟩) x x' p = sym p1 ∙ p2
  where
    y = inverse G x

    p1 : (x' · x) · y ＝ x'
    p1 =
      begin                                          (x' · x) · y
        =⟨ assoc x' x y ⟩                            x' · (x · y)
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
            → x ＝ (inverse G (inverse G x))
inv-olution G@(⟨ _·_ , e , assoc , idp , ivp ⟩) x = unique-inv G (inverse G x) x p
  where
    p : ((inverse G x) · x ＝ e) × (x · (inverse G x) ＝ e)
    p = (snd (pr₂ (ivp x))) , (fst (pr₂ (ivp x)))

-- (a·b) = (a·c) → b = c, multiply by inverse a
lcancel : {S : Set ℓ} → (G : Group S)
        → (a b c : S)
        → (a ·⟨ G ⟩ b) ＝ (a ·⟨ G ⟩ c)
        → b ＝ c
lcancel{ℓ} {S} G@(⟨ _·_ , e , assoc , idp , ivp ⟩) a b c p
  = (sym (lemma2 b)) ∙ lemma1 ∙ (lemma2 c)
  where
    a' = (inverse G a)

    lemma1 : (a' · a) · b ＝ (a' · a) · c
    lemma1 = (assoc a' a b) ∙ (ap (λ x → a' · x) p) ∙ (sym (assoc a' a c))

    lemma2 : (d : S) → (a' · a) · d ＝ d
    lemma2 d = (ap (λ x → x · d) (snd (pr₂ (ivp a)))) ∙ (snd (idp d))

rcancel : {S : Set ℓ} → (G : Group S)
        → (a b c : S)
        → (b ·⟨ G ⟩ a) ＝ (c ·⟨ G ⟩ a)
        → b ＝ c
rcancel{ℓ} {S} G@(⟨ _·_ , e , assoc , idp , ivp ⟩) a b c p
  = (sym (lemma2 b)) ∙ lemma1 ∙ (lemma2 c)
  where
    a' = (inverse G a)

    lemma1 : b · (a · a') ＝ c · (a · a')
    lemma1 = (sym (assoc b a a')) ∙ (ap (λ x → x · a') p) ∙ (assoc c a a')

    lemma2 : (d : S) → d · (a · a') ＝ d
    lemma2 d = (ap (λ x → d · x) (fst (pr₂ (ivp a)))) ∙ (fst (idp d))

inv-comp : {S : Set ℓ} → (G : Group S)
         → (a b : S)
         → (inverse G (a ·⟨ G ⟩ b)) ＝ (inverse G b) ·⟨ G ⟩ (inverse G a)
inv-comp G@(⟨ _·_ , e , assoc , idp , ivp ⟩) a b
  = sym (unique-inv G (a · b) ((inverse G b) · (inverse G a)) (p , q))
  where
    a' = (inverse G a)
    b' = (inverse G b)

    p : ((a · b) · (b' · a') ＝ e)
    p =
      begin                                              (a · b) · (b' · a')
        =⟨ sym (assoc (a · b) b' a') ⟩                   ((a · b) · b') · a'
        =⟨ ap (λ x → x · a') (assoc a b b') ⟩            (a · (b · b')) · a'
        =⟨ ap (λ x → (a · x) · a') (fst (pr₂ (ivp b))) ⟩ (a · e) · a'
        =⟨ ap (λ x → x · a') (fst (idp a)) ⟩             a · a'
        =⟨ (fst (pr₂ (ivp a))) ⟩                         e
      ∎

    q : ((b' · a') · (a · b) ＝ e)
    q =
      begin                                              (b' · a') · (a · b)
        =⟨ sym (assoc (b' · a') a b) ⟩                   ((b' · a') · a) · b
        =⟨ ap (λ x → x · b) (assoc b' a' a) ⟩            (b' · (a' · a)) · b
        =⟨ ap (λ x → (b' · x) · b) (snd (pr₂ (ivp a))) ⟩ (b' · e) · b
        =⟨ ap (λ x → x · b) (fst (idp b')) ⟩             b' · b
        =⟨ (snd (pr₂ (ivp b))) ⟩                         e
      ∎


{- TODO
  modulo group ℤₙ = Fin n
-}

{- TODO
  bijections (functions with inverses)
-}

{- TODO
  cyclic field ℂₙ
-}
