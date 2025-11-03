{-# OPTIONS --without-K --exact-split --rewriting #-}

{-
  random proofs
-}

open import Agda.Primitive
open import logic
open import path
open import function
open import types
open import list
open import bool
open import functor
open import arith
open import op
open import homotopy
open import hlevel
open import hlevel-ex
open import retract
open import equiv
open import equiv-ex
open import joyal
open import univalence

postulate
  LEM : (X : Set ℓ) → X ＋ ¬ X
  FUNEXT : {X : Set ℓ} {Y : Set ℓ₁} {f g : X → Y} → f ~ g → f ＝ g
  -- refl is the only element
  AX-K : {X : Set ℓ} {x : X} (C : (x ＝ x) → Set ℓ₁)
       → C (refl x) → (p : x ＝ x) → C p
  AX-K-comp : {X : Set ℓ} {x : X} (C : (x ＝ x) → Set ℓ₁)
            → (p : C (refl x))
            → AX-K C p (refl x) ＝ p

UIP : {A : Set ℓ} (x : A)
    → (p q : x ＝ x) → p ＝ q
UIP x = AX-K (λ p → ∀ q → p ＝ q) (AX-K (λ r → refl x ＝ r) (refl (refl x)))

-- this is equivalent, subst refl for p
AX-K-rec : {X : Set ℓ} (x : X) (p : x ＝ x) → p ＝ refl x
AX-K-rec x p = UIP x p (refl x)

AX-K-rec-eq : {X : Set ℓ} (x : X) → AX-K-rec x (refl x) ＝ refl (refl x)
AX-K-rec-eq x = AX-K-rec (refl x) (AX-K-rec x (refl x))

{-
  uniqueness: intro on elim thing = thing
-}

uniqλ : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → f ＝ (λ x → f x)
uniqλ f = refl f -- eta moment

uniq× : {A : Set ℓ} {B : Set ℓ₁} → (p : A × B) → p ＝ (fst p , snd p)
uniq× (a , b) = refl (a , b)

uniq⋆ : (a : 𝟙) → ⋆ ＝ a
uniq⋆ = centrality 𝟙-is-singleton

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
ⅉ' {ℓ}{ℓ₁}{A = A} a C ca x p
  = (ȷ (λ x y (q : x ＝ y) → Π D ∶ ((x : A) → (x ＝ y) → Set ℓ₁) ,
                             (D y (refl y) → D x q))
       (λ x → λ D p → p)
       x a p) C ca

{-
  nats are a W-type
-}

data WNatB : Bool → Set where
  wleft  : ⊥ → WNatB false
  wright : 𝟙 → WNatB true

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
  compile-time nonsense
-}

test-len : 1 + 1 ＝ 2
test-len = refl 2

equal : ℕ → ℕ → Bool
equal zero    zero    = true
equal (suc x) zero    = false
equal zero    (suc y) = false
equal (suc x) (suc y) = equal x y

-- bad definition, cannot compute on open term n
-- p : ∀ n → (equal n n) ＝ true
-- p n = refl true

Ctx = Vec ℕ

lookup : {n : ℕ} → Ctx n → Fin n → ℕ
lookup Γ n = Γ !! n

data Expr (n : ℕ) : Set where
  pls : Expr n → Expr n → Expr n
  var : Fin n → Expr n

norm : {n : ℕ} → Expr n → Expr n
norm (pls a b) = pls (norm b) (norm a)
norm (var n) = var n

norm-test : norm (pls (var fz) (var (fs (fz {2})))) ＝ (pls (var (fs fz)) (var fz))
norm-test = refl _

eval : {n : ℕ} → Ctx n → Expr n → ℕ
eval Γ (pls a b) = eval Γ a + eval Γ b
eval Γ (var n) = lookup Γ n

silly-lemma : {a b c d : ℕ} → (a ＝ b) → (c ＝ d) → (a + c ＝ d + b)
silly-lemma {a}{b}{c}{d} p q = transport (λ x → a + c ＝ x + c) p (refl (a + c))
                             ∙ transport (λ x → b + c ＝ b + x) q (refl (b + c))
                             ∙ commutes-+ b d

norm-pres : {n : ℕ} → (Γ : Ctx n) → (e : Expr n) → eval Γ e ＝ eval Γ (norm e)
norm-pres Γ (pls a b) = silly-lemma (norm-pres Γ a) (norm-pres Γ b)
norm-pres Γ (var x) = refl _

test-commut : (x y z : ℕ) → (x + y) + z ＝ z + (y + x)
test-commut x y z = norm-pres (x ∷ y ∷ z ∷ []) -- need better syntax zzz
                              (pls (pls (var fz) (var (fs fz))) (var (fs (fs fz))))

{-
  isabelle is weird, review if this needs univalence
-}

isabelle-cong : {P P' Q Q' : Set ℓ} → is-univalent ℓ
              → P ＝ P' → (P' → Q ＝ Q') → (P → Q) ＝ (P' → Q')
isabelle-cong {P = P}{P'}{Q}{Q'} univalence p＝ q＝
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
    left f = FUNEXT (hom f)

    qmap-is-invertible : invertible qmap
    qmap-is-invertible = qmap⁻¹ , (left , (λ f → FUNEXT (λ p' → l f p')))

    pq-equiv : (P' → Q) ≃ (P' → Q')
    pq-equiv = qmap , invertibles-are-equivalences qmap qmap-is-invertible

    p-cong : (P' → Q) ＝ (P' → Q')
    p-cong = ua univalence (P' → Q) (P' → Q') pq-equiv

{-
  every projection map induces a fibration
-}

fib-proj : {A : Set} → (A → Set) → Σ B ∶ Set , (B → A)
fib-proj {A} fib = (Σ a ∶ A , fib a) , pr₁

proj-fib : {A : Set} → (Σ B ∶ Set , (B → A)) → (A → Set)
proj-fib {A} (B , pr) = λ a → Σ b ∶ B , pr b ＝ a

-- apply extensionality, fibers equal
fib-proj-iso : {A : Set} → (fib : (A → Set)) → (a : A)
             → proj-fib (fib-proj fib) a → fib a
fib-proj-iso fib a ((a' , afib) , a'＝a) = transport fib a'＝a afib

fib-proj-equiv : {A : Set} → (fib : (A → Set)) → (a : A)
               → proj-fib (fib-proj fib) a ≃ fib a
fib-proj-equiv fib a = iso , invertibles-are-equivalences iso proof
  where -- Σ b ∶ (Σ a' ∶ A , fib a') , a' ＝ a*
    iso : proj-fib (fib-proj fib) a → fib a
    iso = fib-proj-iso fib a

    proof : invertible iso
    proof = (λ fa → (a , fa) , refl a) , (λ {(_ , refl _) → refl _}) , refl

-- proj-fib-eq : {is-univalent lzero} → {A : Set}
--             → (proj : (Σ B ∶ Set , (B → A)))
--             → fib-proj (proj-fib proj) ＝ proj
-- -- transport (λ B₁ → B₁ → A) eq pr₁ = pr, doesn't compute
-- proj-fib-eq {uv} {A} (B , pr) = Σ＝ (eq , {!!})
--   where
--     iso : (Σ a ∶ A , Σ b ∶ B , pr b ＝ a) → B
--     iso (_ , b , _) = b

--     iv : invertible iso
--     iv = (λ b → pr b , b , refl _) , (λ {(_ , _ , refl _) → refl _}) , refl

--     equiv : (Σ a ∶ A , Σ b ∶ B , pr b ＝ a) ≃ B
--     equiv = iso , invertibles-are-equivalences iso iv

--     eq : (Σ a ∶ A , Σ b ∶ B , pr b ＝ a) ＝ B
--     eq = ua uv _ _ equiv

-- fib-pr-equiv : {is-univalent lzero} → {A : Set}
--              → (Σ B ∶ Set , (B → A)) ≃ (A → Set)
-- fib-pr-equiv {uv} {A} = proj-fib , invertibles-are-equivalences proj-fib proof
--   where
--     proof : invertible proj-fib
--     proof = fib-proj , proj-fib-eq {uv}
--           , λ fib → FUNEXT (λ a → ua uv _ _ (fib-proj-equiv fib a))

{-
  yoneda
-}

Hom = _＝_

Y : {X : Set ℓ} (x : X) → (y : X) → Set ℓ
Y x = λ y → Hom y x

Id : {X : Set ℓ} → (x : X) → Hom x x
Id = refl

-- Nat A B = ∀ x → A x → B x
_≈_ : {X : Set ℓ} {y : X} {A : X → Set ℓ₁}
    → Nat (Y y) A → Nat (Y y) A → Set (ℓ ⊔ ℓ₁)
η ≈ θ = ∀ x → ∀ Yxy → η x Yxy ＝ θ x Yxy

yoneda-elem : {X : Set ℓ} {x : X} (A : X → Set ℓ₁)
            → Nat (Y x) A → A x
yoneda-elem {x = x} A η = η x (Id x)

-- lifting Hom(x,y) to presheaf A → Set (arrows = maps) is transport
yoneda-nat : {X : Set ℓ} {y : X} (A : X → Set ℓ₁)
           → A y → Nat (Y y) A           -- A p : A y → A x
yoneda-nat {y = y} A a = λ x (p : Y y x) → (transport A (sym＝ p)) a

-- holds definitionally
yoneda-lemma : {X : Set ℓ} {x : X} {A : X → Set ℓ₁}
             → (η : Nat (Y x) A)
             → yoneda-nat A (yoneda-elem A η) ≈ η
yoneda-lemma {A = A} η x (refl .x) = refl (yoneda-elem A η)

{-
  propositional
-}

nn-lem : {P : Set} → ((P ＋ (P → ⊥)) → ⊥) → ⊥
nn-lem f = f (inr (λ p → f (inl p)))

proof-by-negation : {P : Set} → P → ((P → ⊥) → ⊥)
proof-by-negation p f = f p

triple-elim : {P : Set} → (((P → ⊥) → ⊥) → ⊥) → (P → ⊥)
triple-elim = contravariance proof-by-negation

lem→dne : {P : Set} → (P ＋ (P → ⊥)) → ((P → ⊥) → ⊥) → P
lem→dne {P} (inl p) nnp = p
lem→dne {P} (inr p) nnp = lemma p
  where
    lemma : (P → ⊥) → P
    lemma = λ np → ind⊥ (λ _ → P) (nnp np)

dne→lem : (∀ {Q : Set} → ((Q → ⊥) → ⊥) → Q) → {P : Set} → (P ＋ (P → ⊥))
dne→lem p {P} = p nn-lem

-- other direction is easy
pierce→dne : (P : Set) → (∀ (Q : Set) → ((P → Q) → P) → P) → (¬ (¬ P) → P)
pierce→dne P p nnp = p ⊥ (λ np → rec⊥ P (nnp np))

lem→dgp : ∀ {P Q : Set} → (P ＋ (P → ⊥)) → (P → Q) ＋ (Q → P)
lem→dgp (inl p) = inr (λ z → p)
lem→dgp (inr np) = inl (λ p → rec⊥ _ (np p))

two-valued : (∀ (P Q R : Set) → (P → Q) × (Q → P)
                              ＋ (Q → R) × (R → Q)
                              ＋ (R → P) × (P → R))
           → ∀ (P : Set) → ¬ (¬ P) → P
two-valued f P with f P (¬ P) (¬ (¬ P))
...            | inl (np , npp) = λ _ → npp (λ p → np p p)
...            | inr (inl (_ , x)) = λ nnp → rec⊥ _ (nnp (λ p → x (λ np → np p) p))
...            | inr (inr (dne , _)) = dne

-- ω-valued : (∀ (f : ℕ → Set) → Σ n ∶ ℕ , Σ m ∶ ℕ ,
--                                 f n → f m × f m → f n)

{-
  algebras
-}

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

data infalg : Set where
  leaf : infalg
  branch : (ℕ → infalg) → infalg

{- (ℕ→A)→A can only peek at finitely many subtrees by calling ℕ→A -}
infalg-ind : {A : Set} → A → ((ℕ → A) → A) → infalg → A
infalg-ind la ba leaf = la
infalg-ind la ba (branch nb) = ba (λ n → infalg-ind la ba (nb n))

data Badalg : Set where
  co : (𝟙 → Badalg) → Badalg

badalg-rec : {A : Set} → ((𝟙 → A) → A) → Badalg → A
badalg-rec alg (co f) = alg (λ b → badalg-rec alg (f b))

badalg-absurd : ¬ Badalg
badalg-absurd (co f) = badalg-rec (λ f → f ⋆) (co f)

{-
  contradiction leads to bottom, since type families are able to
  distinguish indices by computation
-}

data Bad (E : Set) : ℕ → Set where
  badt : Bad E 0
  badf : E → Bad E 1

badind : ∀{n}{E} → (A : ℕ → Set) → Bad E n → A 0 → (E → A 1) → A n
badind {zero} _ (badt) a0 _ = a0
badind {suc zero} _ (badf e) _ a1 = a1 e
--badind {suc (suc st)} _ ()

{- having a (Bad E 1) gives an E, using pattern matching: bade' (badf x) = x -}
bade : ∀{E} → Bad E 1 → E
bade {E} p = badind (λ n → recℕ 𝟙 (λ n _ → E) n) -- large elim on n
                    p (⋆) (λ z → z)

{- type families respecting indices -}
0≠1 : (0 ＝ 1) → ⊥
0≠1 eq = bade (transport (Bad ⊥) eq (badt))

{-
  a simpler mltt way to do term disequality using large elim
-}

true≠false : true ≠ false
true≠false p = transport (λ t → if t then 𝟙 else ⊥) p ⋆

{-
  for types, use transport
-}

coerce : {A B : Set ℓ} → (A ＝ B) → A → B
coerce = transport id

inhabited≠⊥ : ∀{I} → I → (I ≠ 𝟘)
inhabited≠⊥ i p = coerce p i

{-
  𝟙 ≠ 𝟚 only one is a subsingleton
-}

Bool-not-subsingleton : ¬(is-subsingleton Bool)
Bool-not-subsingleton p = true≠false (p true false)

𝟙≠𝟚 : 𝟙 ≠ Bool
𝟙≠𝟚 p = Bool-not-subsingleton (transport is-subsingleton p 𝟙-is-subsingleton)

{-
  no surjection into the powerset
-}

neg-neq : {A : Set} → A ≠ (¬ A)
neg-neq {A} p = not-a (coerce (sym＝ p) not-a)
  where
    not-a : A → ⊥
    not-a a = (coerce p a) a

cantor : {A : Set} → (f : A → (A → Set)) → surjective f → ⊥
cantor {A} f p = diagonal-neq-any-n (p neg-diagonal)
  where
    neg-diagonal : A → Set
    neg-diagonal n = ¬(f n n)

    diagonal-neq-any-n : ¬ (Σ n ∶ A , f n ＝ neg-diagonal)
    diagonal-neq-any-n (n , p) = neg-neq (ap (λ f → f n) p)

data ⊤₁ : Set₁ where
  ⋆' : ⊤₁

a-not-powerset : {A : Set} → (⊤₁ × A) ≠ (A → Set)
a-not-powerset {A} p = no-surj
                       (transport (λ T → (Σ f ∶ (⊤₁ × A → T) , surjective f))
                                  p (id , id-surjective))
  where
    id-surjective : surjective id
    id-surjective = retraction-surj _ (invertible-retraction _ id-invertible)

    no-surj : ¬(Σ f ∶ (⊤₁ × A → (A → Set)) , surjective f)
    no-surj (f , p) = cantor s s-surj
      where
        s : A → (A → Set)
        s a = f (⋆' , a)

        s-is-f : ∀ x → s (snd x) ＝ f x
        s-is-f (⋆' , x) = refl _

        s-surj : surjective s
        s-surj a = snd (pr₁ (p a)) , s-is-f _ ∙ pr₂ (p a)

{-
  no injection the other way
-}

not-bool-neq : (b : Bool) → b ≠ (not b)
not-bool-neq true ()
not-bool-neq false ()

cantor' : {A : Set} (f : A → (A → Bool)) → ext-surjective f → ⊥
cantor' {A} f p
  = diagonal-neq-any-n (p not-diagonal)
  where
    not-diagonal : A → Bool
    not-diagonal n = not (f n n)

    diagonal-neq-any-n : ¬ (Σ n ∶ A , f n ~ not-diagonal)
    diagonal-neq-any-n (n , p) = not-bool-neq (f n n) (p n)

bool-normal : (b : Bool) → (true ＝ b) ＋ (false ＝ b)
bool-normal true = inl (refl true)
bool-normal false = inr (refl false)

rcantor : {A : Set} → (f : (A → Bool) → A) → injective f → ⊥
rcantor {A} s p = cantor' r (ext-retraction-surj r (s , pf))
  where
    r : A → (A → Bool)
    r a x with LEM (Σ g ∶ (A → Bool) , s g ＝ a × g x ＝ true)
    ... | inl _ = true
    ... | inr _ = false

    pf : (f : A → Bool) → r (s f) ~ f
    pf f x with LEM (Σ (λ g → s g ＝ s f × g x ＝ true)) | bool-normal (f x)
    ...    | inr _ | inr eq = eq
    ...    | inl _ | inl eq = eq
    ...    | inr elim | inl eq = rec⊥ _ (elim (f , refl _ , sym＝ eq))
    ...    | inl (g , (sg＝sf , gx＝t)) | inr eq = sym＝ gx＝t
                                                 ∙ ap (λ f → f x) (p g f sg＝sf)

-- size issues?
-- cantor' : {A : Set} → (f : (A → Set) → A) → injective f → ⊥
-- cantor' {A} f inj = {!!}
--   where
--     R : A → Set₁
--     R a = Σ P ∶ (A → Set) , f P ＝ a × (P a → ⊥)

{-
  how do we talk about function equality?
  well I don't see how to do it uniformly (extensionality is this assumption)
  but we can prove disequalities by examining points

  this can give type disequalities (𝟙 → 𝟚) ≠ 𝟙
  so we can talk about big function spaces, but not small (nonempty) ones?
-}

auto-subsingleton : ∀ (A : Set) → is-subsingleton A → (f g : A → A) → f ＝ g
auto-subsingleton A p f g = FUNEXT (λ a → p (f a) (g a))

1→0-subsingleton : is-subsingleton (𝟙 → 𝟘)
1→0-subsingleton f g = rec⊥ (f ＝ g) (f ⋆)

neg-nequiv : {A : Set} → (A ≃ (¬ A)) → ⊥
neg-nequiv {A} (e , p) = not-a ((inverse e p) not-a)
  where
    not-a : A → ⊥
    not-a a = e a a

-- tseq : ℕ → Set
-- tseq zero = 𝟘
-- tseq (suc n) = 𝟙 ＋ tseq n

-- tfinite : Set ℓ → Set ℓ
-- tfinite X = Σ n ∶ ℕ , Σ f ∶ (X → Fin n) , injective f

-- inj-nat-tseq : Σ f ∶ (ℕ → Set) , injective f
-- inj-nat-tseq = tseq , test
--   where
--     test : injective tseq
--     test zero zero p = refl zero
--     test zero (suc m) p = rec⊥ _ (transport (λ A → A → 𝟘) p id (inl ⋆))
--     test (suc n) zero p = rec⊥ _ (transport (λ A → A → 𝟘) (sym＝ p) id (inl ⋆))
--     test (suc n) (suc m) p = {!(test n m)!} -- not provable

-- no-surj-fin-nat : ¬(Σ n ∶ ℕ , Σ f ∶ (ℕ → Fin n) , injective f)
-- no-surj-fin-nat = {!!}

-- no-fin-surj-set : ¬(tfinite Set)
-- no-fin-surj-set (n , f , p) = no-surj-fin-nat (n , _ , test)
--   where
--     test : injective (f ∘ pr₁ inj-nat-tseq)
--     test = inj-comp (pr₁ inj-nat-tseq) (pr₂ inj-nat-tseq) f p

-- 𝟙-endo-small : (f : (𝟙 → 𝟙) → Set) → surjective f → ⊥
-- 𝟙-endo-small f p = {!!}

{-
  involutions on universes
-}

-- negation disproves f^n = f^n+1 for all n
all-auto-absurd : ¬(∀ (f : Set → Set) → (A : Set) → f A ＝ A)
all-auto-absurd f = neg-neq (sym＝ (f (¬_) 𝟙))

-- this argument generalises to all f^n > 1
all-invol-absurd : ¬(∀ (f : Set → Set) → (A : Set) → f (f A) ＝ A)
all-invol-absurd f = true≠false (ap (λ f → f (λ _ → true)) bad)
  where
    p : is-subsingleton ((𝟙 → Bool) → Bool)
    p = transport is-subsingleton (sym＝ (f (λ X → X → Bool) 𝟙)) 𝟙-is-subsingleton

    bad : (λ _ → true) ＝ (λ _ → false)
    bad = p _ _

-- true for all odd f^n
auto3-prop-absurd : ¬(∀ (f : Set → Set) → (A : Set) → is-prop A → f (f (f A)) ＝ A)
auto3-prop-absurd f = neg3-neq (sym＝ (f (¬_) 𝟙 𝟙-is-subsingleton))
  where
    neg3-neq : {A : Set} → A ≠ (¬(¬(¬ A)))
    neg3-neq {A} p = na (coerce (sym＝ p) (proof-by-negation na))
      where
        test : A → ¬(¬(¬ A)) → ⊥
        test a nnna = nnna (proof-by-negation a)

        na : A → ⊥
        na a = test a (coerce p a)

endo-2-prop : (∀ (f : Set → Set) → (A : Set) → is-prop A → f (f A) ＝ A)
            → lem lzero -- : is-prop X → X ＋ ¬X
endo-2-prop f X x-is-prop = prop-dne decidable-is-prop nn-lem
  where
    prop-dne : ∀ {X} → is-prop X → ¬(¬ X) → X
    prop-dne {X} x-is-prop nnp = coerce (f (¬_) X x-is-prop) nnp

    nx-prop : ∀ {X} → is-prop X → is-prop (¬ X)
    nx-prop x-is-prop nx nx' = FUNEXT (λ x → 𝟘-is-subsingleton (nx x) (nx' x))

    decidable-is-prop : is-prop (X ＋ (¬ X))
    decidable-is-prop (inl x) (inl x') = ap inl (x-is-prop x x')
    decidable-is-prop (inr nx) (inr nx') = ap inr (nx-prop x-is-prop nx nx')
    decidable-is-prop (inl x) (inr nx) = rec⊥ _ (nx x)
    decidable-is-prop (inr nx) (inl x) = rec⊥ _ (nx x)

-- what about even differences?
-- endo-31-prop : (∀ (f : Set → Set) → (A : Set) → is-prop A → f (f (f A)) ＝ f A)
--              → lem lzero
-- endo-31-prop f X x-is-prop = {!!}
--   where
--     test : {!!}
--     test = f (λ X → {!!}) X x-is-prop

{-
  effective quotients
-}

record Quot (A : Set ℓ) (R : A → A → Set ℓ₁) : Set (ℓ ⊔ ℓ₁) where
  constructor quo
  field
   c1 : ∀ x → R x x
   c2 : ∀ x y → R x y → R y x
   c3 : ∀ x y z → R x y → R y z → R x z

qtest1 : Quot ℕ _＝_
qtest1 = quo refl (λ x y → sym＝) (λ x y z → trans＝)

-- intro
record _/_ (A : Set ℓ) (R : A → A → Set ℓ₁) : Set (ℓ ⊔ ℓ₁) where
  constructor ⟦_⟧[_]
  field
    e : A
    quot : Quot A R

qtest2 : ℕ / _＝_
qtest2 = ⟦ 0 ⟧[ qtest1 ]

postulate
  qax : {A : Set ℓ} {R : A → A → Set ℓ₁}
      → (Q : Quot A R)
      → {a b : A} → R a b
      → ⟦ a ⟧[ Q ] ＝ ⟦ b ⟧[ Q ]

  qdest : {A : Set ℓ} {R : A → A → Set ℓ₁} {Q : Quot A R}
        → (L : A / R → Set ℓ₂)
        -- every map A → L respecting the quotient
        → (l : (a : A) → L ⟦ a ⟧[ Q ])
        → (p : ∀ x y → (r : R x y) → subst L (qax Q r) (l x) ＝ l y)
        -- induces a map A/R → L
        → (q : A / R) → L q

  qcomm : {A : Set ℓ} {R : A → A → Set ℓ₁} {Q : Quot A R}
        → (L : A / R → Set ℓ₂)
        → (l : (a : A) → L ⟦ a ⟧[ Q ])
        → (p : ∀ x y → (r : R x y) → subst L (qax Q r) (l x) ＝ l y)
        -- and this map agrees with l a
        → (a : A) → qdest L l p ⟦ a ⟧[ Q ] ＝ l a

  qeff : {A : Set ℓ} {R : A → A → Set ℓ₁}
       → (Q : Quot A R)
       → (x y : A)
       → ⟦ x ⟧[ Q ] ＝ ⟦ y ⟧[ Q ]
       → R x y

-- quniq : {A : Set ℓ} {R : A → A → Set ℓ₁} {Q : Quot A R}
--       → (L : A / R → Set ℓ₂)
--       → (l : (a : A) → L ⟦ a ⟧[ Q ])
--       → (p : ∀ x y → (r : R x y) → subst L (qax Q r) (l x) ＝ l y)
--       → (z : (q : A / R) → L q)
--       → (∀ a → z ⟦ a ⟧[ Q ] ＝ l a)
--       → (q : A / R) → z q ＝ qdest L l p q
-- quniq {Q = Q} L l p z zp q = {!!}
