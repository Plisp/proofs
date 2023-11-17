{-# OPTIONS --without-K --exact-split #-}

{-
  random proofs: no arith and op since those are useful
-}

open import logic
open import path
open import types
open import hlevel
open import retract
open import equiv
open import univalence

{-
  I love recursion principles
-}

ackermann : ℕ → ℕ → ℕ
ackermann = recℕ mzero msucc
  where
    mzero : ℕ → ℕ
    mzero = λ n → suc n
    -- from ackermann m _, produce ackermann (suc m) _
    msucc : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
    msucc = λ m am → recℕ (am 1) (λ n a-sm-n → am a-sm-n)

{-
  an empty initial algebra
-}

data badalg : Set where
  co : (Bool → badalg) → badalg

badalg-rec : {A : Set} → ((Bool → A) → A) → (t : badalg) → A
badalg-rec alg (co f) = alg (λ b → badalg-rec alg (f b))

badalg-contra : ¬ badalg
badalg-contra (co f) = badalg-rec (λ f → f true) (co f)

{-
  TODO prove these
-}

postulate
  funext :
    {X : Set ℓ} {Y : Set ℓ₁} {f g : X → Y} → f ~ g → f ＝ g

isabelle-cong : {P P' Q Q' : Set ℓ} → is-univalent ℓ
              → P ＝ P' → (P' → Q ＝ Q') → (P → Q) ＝ (P' → Q')
isabelle-cong {ℓ} {P}{P'}{Q}{Q'} univalence p＝ q＝
  = transport (λ t → (t → Q) ＝ (P' → Q')) (sym＝ p＝) p-cong
  where
    qmap : (P' → Q) → (P' → Q')
    qmap pq p' = subst id (q＝ p') (pq p')
    qmap⁻¹ : (P' → Q') → (P' → Q)
    qmap⁻¹ pq p' = subst id (sym＝ (q＝ p')) (pq p')

    l : (f : P' → Q') (p : P')
      → subst id (q＝ p) (subst id (sym＝ (q＝ p)) (f p)) ＝ (f p)
    l f p = let qq = (q＝ p) in
              (transport∙ (sym＝ qq) _ _)
            ∙ (ap (λ t → transport id t _) (iv∙p＝refl qq))

    g : (f : P' → Q) → (p : P') → (qmap⁻¹ ∘ qmap) f p ＝ f p
    g f p = let qq = (q＝ p) in
              (transport∙ qq (sym＝ qq) (f p))
            ∙ (ap (λ t → transport id t (f p)) (p∙iv＝refl qq))

    hom : (f : P' → Q) → (qmap⁻¹ ∘ qmap) f ~ f
    hom f p' = g f p'

    left : (f : P' → Q) → (qmap⁻¹ ∘ qmap) f ＝ id f
    left f = funext (hom f)

    qmap-is-invertible : invertible qmap
    qmap-is-invertible = qmap⁻¹ , (left , (λ f → funext (λ p' → l f p')))

    pq-equiv : (P' → Q) ≃ (P' → Q')
    pq-equiv = qmap , invertibles-are-equivalences qmap qmap-is-invertible

    p-cong : (P' → Q) ＝ (P' → Q')
    p-cong = ua univalence (P' → Q) (P' → Q') pq-equiv

{-
  new type: manual boolean
-}

𝟚 = 𝟙 ＋ 𝟙
𝟚-ind : (A : 𝟚 → Set ℓ) → A (inl ⋆) → A (inr ⋆) → ((b : 𝟚) → A b)
𝟚-ind A a₀ a₁ = ind＋ A
                (ind⊤ (λ (x : 𝟙) → (A (inl x))) a₀)
                (ind⊤ (λ (x : 𝟙) → (A (inr x))) a₁)

{-
  uniqueness: intro on elim thing = thing
-}

uniqλ : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → f ＝ (λ x → f x)
uniqλ f = refl f -- eta moment

uniq× : {A : Set ℓ} {B : Set ℓ₁} → (p : A × B) → p ＝ (fst p , snd p)
uniq× (a , b) = refl (a , b)

uniq⋆ : (a : 𝟙) → ⋆ ＝ a
uniq⋆ = centrality ⊤ 𝟙-is-singleton

{-
  \j the fun way!
-}

-- ∀ x y equal, choosing a = y, then apply ⅉ, 'coerce' back
ȷ' : {A : Set ℓ} (C : (x y : A) → (x ＝ y) → Set ℓ₁)
   → ((x : A) → C x x (refl x))
   → (x y : A) (p : x ＝ y) → C x y p
ȷ' C f x y p = ⅉ x (λ y p → C x y p) (f x) y p

ⅉ' : {A : Set ℓ} (a : A)
   → (C : (x : A) → (x ＝ a) → Set ℓ₁)
   → C a (refl a)
   → (x : A) (p : x ＝ a) → C x p
ⅉ' {ℓ}{ℓ₁} {A} a C ca x p -- quantify over ∀!! such predicates and their 'base'
  = (ȷ (λ x y (q : x ＝ y) → Π D ∶ ((x : A) → (x ＝ y) → Set ℓ₁) ,
                             (D y (refl y) → D x q))
       (λ x → λ D p → p)
       x a p) C ca

{-
  nats are a W-type
-}

data WNatB : Bool → Set where
  wleft  : ⊥ → WNatB false
  wright : ⊤ → WNatB true

WNat : Set
WNat = W Bool WNatB

wzero : WNat
wzero = false ◂ (λ {(wleft ())})

wsuc : WNat → WNat
wsuc n = true ◂ (λ _ → n)

wrec : {C : Set} → WNat → C → (WNat → C → C) → C
wrec (false ◂ _) z _ = z
wrec (true  ◂ f) z s = s (f (wright ⋆)) (wrec (f (wright ⋆)) z s)

{-
  double negation translation
-}

lem : {P : Set} → ((P ＋ (P → ⊥)) → ⊥) → ⊥
lem f = f (inr (λ p → f (inl p)))

proof-by-negation : {P : Set} → P → ((P → ⊥) → ⊥)
proof-by-negation p f = f p

triple-elim : {P : Set} → (((P → ⊥) → ⊥) → ⊥) → (P → ⊥)
triple-elim f p = f (proof-by-negation p)

lem→proof-by-contradiction : {P : Set} → (P ＋ (P → ⊥)) → ((P → ⊥) → ⊥) → P
lem→proof-by-contradiction {P} lem nnp = ind＋ (λ _ → P) id lemma lem
  where
    lemma : (P → ⊥) → P
    lemma = λ np → ind⊥ (λ _ → P) (nnp np)

{-
  contradiction leads to bottom
-}

data Bad : ℕ → Set where
  badt : ⊤ → Bad 0
  badf : ⊥ → Bad 1

destroy : Bad 1 → ⊥
destroy (badf void) = void

negation : (0 ＝ 1) → ⊥
negation eq = destroy (transport Bad eq (badt ⋆))

{-
  bounded vectors
-}

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

length : {A : Set} {n : ℕ} → Vec A n → ℕ
length {_} {n} _ = n

_!!_ : {A : Set} {n : ℕ} → Vec A n → Fin n → A
(a ∷ as) !! fz   = a
(a ∷ as) !! fs b = as !! b

_++_ : {A : Set} {x y : ℕ} → Vec A x → Vec A y → Vec A (x + y)
[]       ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

{-
  compile-time tests !
-}

test-len : (length (1 ∷ 2 ∷ [])) ＝ 2
test-len = refl 2

equal : ℕ → ℕ → Bool
equal 0       0       = true
equal (suc x) 0       = false
equal 0       (suc y) = false
equal (suc x) (suc y) = equal x y

-- bad definition
-- p : ∀ n → (equal n n) ＝ true
-- p n = refl true

{-
  functor laws for A -> Vec A n
-}

map : {A B : Set} {n : ℕ} → (f : A → B) → Vec A n → Vec B n
map f []        = []
map f (a ∷ as) = (f a) ∷ (map f as)

map-id : {A : Set} {n : ℕ} (xs : Vec A n) → (map id xs) ＝ xs
map-id [] = refl _
map-id (x ∷ xs) =
  begin
                               map id (x ∷ xs)
    =⟨⟩                        (id x) ∷ (map id xs)
    =⟨⟩                        x ∷ (map id xs)
    =⟨ ap (x ∷_) (map-id xs) ⟩ x ∷ xs
  ∎

map-compose : {A B C : Set} {n : ℕ} (f : B → C) (g : A → B) (xs : Vec A n)
            → map (f ∘ g) xs ＝ map f (map g xs)
map-compose f g [] =
  begin map (f ∘ g) []
    =⟨⟩ []
    =⟨⟩ map f []
    =⟨⟩ map f (map g [])
  ∎
map-compose f g (x ∷ xs) =
  begin
                                              map (f ∘ g) (x ∷ xs)
    =⟨⟩                                       (f ∘ g) x ∷ map (f ∘ g) xs
    =⟨⟩                                       f (g x) ∷ map (f ∘ g) xs
    =⟨ ap (f (g x) ∷_) (map-compose f g xs) ⟩ f (g x) ∷ map f (map g xs)
    =⟨⟩                                       map f ((g x) ∷ map g xs)
    =⟨⟩                                       map f (map g (x ∷ xs))
  ∎
