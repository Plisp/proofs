{-# OPTIONS --without-K --exact-split #-}

{-
  random proofs
-}

open import logic
open import path
open import types
-- open import list
open import bool
-- open import functor
open import arith
-- open import op
open import homotopy
open import hlevel
open import hlevel-ex
-- open import retract
-- open import retract-ex
open import equiv
open import equiv-ex -- unused
open import joyal
open import univalence

{-
  I love recursion principles
-}

plus : ℕ → ℕ → ℕ  -- 0-plus and vv a-plus → a+1 plus
plus = recℕ (λ b → b) (λ a plus-a → λ b → suc (plus-a b))

-- unpack and repack alg until lift bottoms out (ignores its argument)
-- (inl ⋆ : (1+ℕ)) --⋆--> (inl ⋆)
--       ^                   v
--     Z : ℕ       - - -> alg-zero
--
-- if X is a coalgebra, this may not terminate as iso will
-- unwrap indefinitely
--
-- init : {A X : Set} {P : Set → Set}
--      → (∀{A B : Set} → (A → B) → (P A → P B))
--      → (P A → A) → (X → P X) → (X → A)
-- init lift alg iso = alg ∘ (lift (init lift alg iso)) ∘ iso

ackermann : ℕ → ℕ → ℕ
ackermann = recℕ mzero msucc
  where
    mzero : ℕ → ℕ
    mzero = λ n → suc n
    -- from ackermann m _, produce ackermann (suc m) _
    msucc : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
    msucc = λ m am → recℕ (am 1) (λ n a-sm-n → am a-sm-n)

reindex : {J I : Set} {A : I → Set} (α : J → I)
        → Σ j ∶ J , A (α j) → Σ i ∶ I , A i
reindex α (p1 , p2) = (α p1 , p2)

{-
  what models this?
-}

data infalg : Set where
  leaf : infalg
  branch : (ℕ → infalg) → infalg

{- (ℕ→A)→A can only peek at finitely many subtrees by calling ℕ→A -}
infalg-ind : {A : Set} → A → ((ℕ → A) → A) → infalg → A
infalg-ind la ba leaf = la
infalg-ind la ba (branch nb) = ba (λ n → infalg-ind la ba (nb n))

{-
  an empty initial algebra
-}

data badalg : Set where
  co : (⊤ → badalg) → badalg

badalg-rec : {A : Set} → ((⊤ → A) → A) → (t : badalg) → A
badalg-rec alg (co f) = alg (λ b → badalg-rec alg (f b))

badalg-contra : ¬ badalg
badalg-contra (co f) = badalg-rec (λ f → f ⋆) (co f)

{-
  isabelle is weird, review if this needs univalence
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
ⅉ' {ℓ}{ℓ₁} {A} a C ca x p
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

data Bad (E : Set) : ℕ → Set where
  badt : Bad E 0
  badf : E → Bad E 1

badind : ∀{n}{E} → (A : ℕ → Set) → Bad E n → (A 0) → (E → A 1) → (A n)
badind {zero} _ (badt) = λ z _ → z
badind {suc zero} _ (badf e) = λ _ z → z e
badind {suc (suc st)} _ ()

{- having a (Bad E 1) gives an E -}
bade : ∀{E} → Bad E 1 → E
bade {E} p = badind (λ n → recℕ ⊤ (λ n _ → E) n)
                    p (⋆) (λ z → z)

0≠1 : (0 ＝ 1) → ⊥ {- this ⊥ could be any type E -}
0≠1 eq = bade (transport (Bad ⊥) eq (badt))

{- bot is initial in maps, probably requires univalence -}
-- bot-uniqueness : (∀{E} → A → E)) → A = ⊥
-- bot-uniqueness = ?

{- for types, use maps -}
data Test (E : Set) : Set → Set₁ where
  conA : Test E ⊥
  conB : E → Test E E

tind : ∀{E}{t} → (A : Set → Set) → Test E t → A ⊥ → A E → (A t)
tind _ (conA) at _ = at
tind _ (conB _) _ ae = ae

tdest : ∀{E} → Test E ⊤ → E
tdest {E} p = bad ⋆
  where {- maps into E -}
    bad : ⊤ → E
    bad = tind (λ t → (t → E)) p (rec⊥ E) id

⊤≠⊥ : (⊥ ＝ ⊤) → ⊥
⊤≠⊥ p = tdest (transport (Test ⊥) p (conA))

{-
  compile-time tests !
-}

test-len : 1 + 1 ＝ 2
test-len = refl 2

equal : ℕ → ℕ → Bool
equal 0       0       = true
equal (suc x) 0       = false
equal 0       (suc y) = false
equal (suc x) (suc y) = equal x y

-- bad definition, cannot compute on open term n
-- p : ∀ n → (equal n n) ＝ true
-- p n = refl true
