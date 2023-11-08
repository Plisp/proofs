{-# OPTIONS --without-K --exact-split --safe #-}

{-
  univalent math, hott chapter 3
-}

open import Agda.Primitive
open import logic
open import types
open import paths

{-
  -1-type (contractible)
-}

is-center : (X : Set ℓ) → X → Set ℓ
is-center X c = (x : X) → c ＝ x

is-contr : Set ℓ → Set ℓ
is-contr X = Σ c ∶ X , is-center X c

𝟙-is-singleton : is-contr 𝟙
𝟙-is-singleton = ⋆ , ind⊤ (λ x → ⋆ ＝ x) (refl ⋆)

center : (X : Set ℓ) → is-contr X → X
center X (c , p) = c

centrality : (X : Set ℓ) (i : is-contr X) → (x : X) → center X i ＝ x
centrality X (c , p) = p

singleton-type : {X : Set ℓ} → X → Set ℓ
singleton-type {ℓ} {X} x = Σ c ∶ X , c ＝ x

singleton-type-center : {X : Set ℓ} (x : X) → singleton-type x
singleton-type-center x = (x , refl x)

-- refl makes this trivial, since we have any (x, x ＝ y) is simply (x, refl x)
singleton-type-centered : {X : Set ℓ} (x : X) (σ : singleton-type x)
                        → singleton-type-center x ＝ σ
singleton-type-centered x (x , refl x) = refl (x , refl x)

 -- is-contr (Σ y , y ＝ x) is of the form Σ c , (x , refl x) ＝ c
singleton-types-are-singletons : (X : Set ℓ) (x : X)
                               → is-contr (singleton-type x)
singleton-types-are-singletons X x
  = singleton-type-center x , singleton-type-centered x

-- (subtype) singletons but maybe not inhabited
is-subsingleton : Set ℓ → Set ℓ
is-subsingleton X = (x y : X) → x ＝ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = ind⊥ (λ x → (x ＝ y)) x

is-prop = is-subsingleton

singletons-are-subsingletons : (X : Set ℓ) → is-contr X → is-subsingleton X
singletons-are-subsingletons X (c , p) x y = sym＝ (p x) ∙ p y

pointed-subsingleton→singleton : (X : Set ℓ) → X
                               → is-subsingleton X → is-contr X
pointed-subsingleton→singleton X x s = (x , s x)

{-
  n-types/groupoids ↔ hlevel n+2
-}

0-type : Set ℓ → Set ℓ
0-type X = (x y : X) → is-subsingleton (x ＝ y)

is-set = 0-type

1-type : Set ℓ → Set ℓ
1-type X = {x y : X} (p q : x ＝ y) → is-subsingleton (p ＝ q)

_is-of-hlevel_ : Set ℓ → ℕ → Set ℓ
X is-of-hlevel zero    = is-contr X
X is-of-hlevel (suc n) = (x x' : X) → ((x ＝ x') is-of-hlevel n)

-- if all points connected, then all 2-paths are trivial
subsingleton→set : (X : Set ℓ) → is-subsingleton X → is-set X
subsingleton→set X ss = proof
  where
    lemma0 : {x y : X} (p : x ＝ y) → (ss x x) ∙ p ＝ (ss x y)
    lemma0 {x} {y} p = sym＝ (transport-startpoint p (ss x x)) ∙ apd (λ - → ss x -) p
    -- x＝x ∙ p ＝ transp(λ - → x ＝ -) p (ss x x) | (transp (λ - → x ＝ -) p x＝x) ＝ x＝y
    -- sym＝ (transport-startpoint p (ss x x))   ∙ apd (λ - → ss x -) p
    --
    -- any path factors through the subsingleton proof
    -- x -p→ y
    --  \    ↑
    ---  ↓  /
    --    x
    -- p ∙ q ＝ r  ≃  q ＝ sym＝ p ∙ r, or just make holes and C-c C-a
    lemma : {x y : X} (p : x ＝ y) → p ＝ sym＝ (ss x x) ∙ (ss x y)
    lemma {x} {y} p = p＝refl∙p p ∙ ap (λ e → e ∙ p) (sym＝ (iv∙p＝refl (ss x x)))
                    ∙ assoc∙ (sym＝ (ss x x)) (ss x x) p
                    ∙ ap (λ e → sym＝ (ss x x) ∙ e) (lemma0 p)

    proof : (x y : X) (p q : x ＝ y) → p ＝ q
    proof x y p q = lemma p ∙ sym＝ (lemma q)

-- the levels are upper closed
hlevel-suc : (X : Set ℓ) (n : ℕ)
           → X is-of-hlevel n → X is-of-hlevel (suc n)
hlevel-suc X zero    = λ h → λ x y →
                         let k = singletons-are-subsingletons X h in
                             (k x y , subsingleton→set X k x y (k x y))
-- lift H (suc n) X using X = (x＝y) in ind (H n T -> H (suc n) T)
hlevel-suc X (suc n) = λ h → λ x y → hlevel-suc (x ＝ y) n (h x y)

-- equalities are of a hlevel that's one less
hlevel-eq : {X : Set ℓ} {n : ℕ}
          → X is-of-hlevel (suc n)
          → (x y : X) → (x ＝ y) is-of-hlevel n
hlevel-eq {ℓ}{X} {n} p x y = p x y

𝟘-is-set : is-set 𝟘
𝟘-is-set = subsingleton→set 𝟘 𝟘-is-subsingleton

{-
  decidable
-}

decidable : Set ℓ → Set ℓ
decidable A = A ＋ ¬ A

has-decidable-equality : Set ℓ → Set ℓ
has-decidable-equality A = (x y : A) → decidable (x ＝ y)

is-empty : Set ℓ → Set ℓ
is-empty X = ¬ X

LEM LEM' : ∀ ℓ → Set (lsuc ℓ)
LEM ℓ = (X : Set ℓ) → is-prop X → decidable X
LEM' ℓ = (X : Set ℓ) → is-subsingleton X → is-contr X ＋ is-empty X

{-
  retracts
-}

-- right inverse
has-section : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
has-section {ℓ}{ℓ₁} {X}{Y} f = Σ g ∶ (Y → X) , f ∘ g ~ id

-- X type is a retract of Y
_◁_ : Set ℓ → Set ℓ₁ → Set (ℓ ⊔ ℓ₁)
X ◁ Y = Σ f ∶ (Y → X) , has-section f

retraction : {X : Set ℓ} {Y : Set ℓ₁} → X ◁ Y → (Y → X)
retraction (r , s , η) = r

section : {X : Set ℓ} {Y : Set ℓ₁} → X ◁ Y → (X → Y)
section (r , s , η) = s

is-retract : {X : Set ℓ} {Y : Set ℓ₁} → (p : X ◁ Y)
           → retraction p ∘ section p ~ id
is-retract (r , s , η) = η

refl◁ : (X : Set ℓ) → X ◁ X
refl◁ X = id , id , refl

_◁∙_ : {X : Set ℓ} {Y : Set ℓ₁} {Z : Set ℓ₂} → X ◁ Y → Y ◁ Z → X ◁ Z
(r , s , η) ◁∙ (r' , s' , η') = r ∘ r' , s' ∘ s , λ x → ap r (η' (s x)) ∙ η x

_◁⟨_⟩_ : (X : Set ℓ) {Y : Set ℓ₁} {Z : Set ℓ₂} → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ x◁y ⟩ y◁z = x◁y ◁∙ y◁z
infixr 2 _◁⟨_⟩_

-- a natural transformation between two fibrations
Nat : {X : Set ℓ} → (X → Set ℓ₁) → (X → Set ℓ₂) → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
Nat A B = ∀ x → A x → B x
-- gives a map between their total spaces
NatΣ : {X : Set ℓ} {A : X → Set ℓ₁} {B : X → Set ℓ₂} → Nat A B → Σ A → Σ B
NatΣ τ (x , a) = (x , τ x a)

Σ-retract : {X : Set ℓ} {A : X → Set ℓ₁} {B : X → Set ℓ₂}
          → ((x : X) → A x ◁ B x) → Σ A ◁ Σ B
Σ-retract {ℓ}{ℓ₁}{ℓ₂} {X} {A} {B} ρ = NatΣ r , NatΣ s , η
  where
    r = λ x → retraction (ρ x)
    s = λ x → section (ρ x)
    η' : (x : X) → r x ∘ s x ~ id
    η' x = is-retract (ρ x)

    η : NatΣ r ∘ NatΣ s ~ id
    η (x , a) = ap (λ - → (x , -)) (η' x a)

transport-is-retraction : {X : Set ℓ} (A : X → Set ℓ₁) {x y : X} (p : x ＝ y)
                        → transport A p ∘ transport A (sym＝ p) ~ id
transport-is-retraction A p = id~ (transport-p-sym p)

transport-is-section : {X : Set ℓ} (A : X → Set ℓ₁) {x y : X} (p : x ＝ y)
                     → transport A (sym＝ p) ∘ transport A p ~ id
transport-is-section A p = id~ (transport-sym-p p)

-- retraction similar to above but only at basepoints X ◁ Y =A Y=
Σ-reindex-retract : {X : Set ℓ} {Y : Set ℓ₁} {A : X → Set ℓ₂}
                  → (r : Y → X) → has-section r
                  → (Σ x ∶ X , A x) ◁ (Σ y ∶ Y , A (r y))
Σ-reindex-retract {ℓ}{ℓ₁}{ℓ₂} {X} {Y} {A} r (s , η) = ar , as , aη
  where
   ar : Σ (A ∘ r) → Σ A
   ar (y , a) = (r y , a)

   as : Σ A → Σ (A ∘ r) -- A (id x) -> A (r (s x))
   as (x , a) = (s x , transport A (sym＝ (η x)) a)

   -- to-Σ does a transport along the first equality which is cancelled
   aη : ((x , a) : Σ A) → (r (s x) , transport A (sym＝ (η x)) a) ＝ (x , a)
   aη (x , a) = to-Σ＝ (η x , transport-is-retraction A (η x) a)

retract-of-singleton : {X : Set ℓ} {Y : Set ℓ₁}
                     → Y ◁ X → is-contr X → is-contr Y
retract-of-singleton (f , g , p) contr = f (center _ contr) , centr
  where
    centr : ∀ y → f (center _ contr) ＝ y
    centr y = ap f (centrality _ contr (g y)) ∙ (p y)

{-
  Voevodsky's equivalence
-}

-- space: witnesses x × f x = y
fiber : {X :  Set ℓ} {Y : Set ℓ₁} (f : X → Y) → Y → Set (ℓ ⊔ ℓ₁)
fiber {ℓ}{ℓ₁} {X}{Y} f y = Σ x ∶ X , f x ＝ y

fiber-base : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
           → fiber f y → X
fiber-base (x , p) = x

fiber-id : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
         → (w : fiber f y) → f (fiber-base w) ＝ y
fiber-id (x , p) = p

-- the fibre (preimage) of all y : Y under f is unique (size 1)
-- the proof is also unique, via the characterisation of Σ identity
is-equiv : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
is-equiv {ℓ}{ℓ₁} {X}{Y} f = Π y ∶ Y , is-contr (fiber f y)

_≃_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
X ≃ Y = Σ f ∶ (X → Y) , is-equiv f
infix 5 _≃_

equiv-fn : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → X → Y
equiv-fn (f , i) = f

id-is-equiv : (X : Set ℓ) → is-equiv id
id-is-equiv = singleton-types-are-singletons

refl≃ : (X : Set ℓ) → X ≃ X
refl≃ X = id , id-is-equiv X

-- inverses - center is p , Σ x, f x ＝ y
inverse : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) → is-equiv f → (Y → X)
inverse f equiv y = fiber-base (center (fiber f y) (equiv y))

{-
  relationship with invertibles
-}

invertible : {A : Set ℓ} {B : Set ℓ₁} (f : A → B) → Set (ℓ ⊔ ℓ₁)
invertible {ℓ}{ℓ₁} {A}{B} f = Σ g ∶ (B → A) , g ∘ f ~ id × f ∘ g ~ id

-- the easy direction
inverses-are-sections : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) (e : is-equiv f)
                      → f ∘ inverse f e ~ id
inverses-are-sections f e y = fiber-id (center (fiber f y) (e y))

inverse-centrality : {X : Set ℓ} {Y : Set ℓ₁}
                     (f : X → Y) (e : is-equiv f) (y : Y) (t : fiber f y)
                   → (inverse f e y , inverses-are-sections f e y) ＝ t
inverse-centrality f e y = centrality (fiber f y) (e y)

inverses-are-retractions : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) (e : is-equiv f)
                         → inverse f e ∘ f ~ id
inverses-are-retractions f e x = ap pr₁ r
  where
    q : ∀ fb → (center _ (e (f x))) ＝ fb
    q = centrality _ (e (f x))
    -- inverse is just the base of the single fiber
    r : center (fiber f (f x)) (e (f x)) ＝ (x , refl (f x))
    r = q (x , refl (f x))

equivs-are-invertible : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
                      → is-equiv f → invertible f
equivs-are-invertible f e = inverse f e ,
                            inverses-are-retractions f e ,
                            inverses-are-sections f e

-- the hard direction

-- invertibles-are-equivs : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y)
--                        → invertible f → is-equiv f
-- invertibles-are-equivs {ℓ}{ℓ₁} {X} f (g , gf , fg) y = proof
--   where
--     -- p1 : ∀ (x : X) → (f x ＝ y) ◁ (g (f x) ＝ g y)
--     -- p1 x = (λ x＝gy → (ap f x＝gy) ∙ fg y ) ,
--     --        (λ fx＝y → sym＝ (sym＝ (ap g fx＝y) ∙ gf x)) ,
--     --        (λ p → (sym＝ (ap f (fg x)) ∙ fg y) ＝ refl)
--     --sym＝ (ap g fx＝y) ∙ gf x

--     -- want to show this type is a retract of a singleton
--     -- fibre type (Σ x , f x ＝ y) ◁ (Σ x , x ＝ g y) ◁ (Σ x , g y ＝ x)
--     -- use X ◁⟨x◁y⟩ y◁z
--     fiber-is-singleton-Σ-retract : (fiber f y) ◁ (Σ x ∶ X , x ＝ (g y))
--     fiber-is-singleton-Σ-retract
--       = (Σ x ∶ X , f x ＝ y) ◁⟨ {!!} ⟩ (Σ x ∶ X  , g (f x) ＝ g y)
--                             ◁⟨ {!!} ⟩ (refl◁ (Σ x ∶ X , x ＝ (g y)))

--     -- giving is-contr Σ c ∶ X , c ＝ (g y)
--     fiber-is-singleton : (fb : fiber f y) → (g y , fg y) ＝ fb
--     fiber-is-singleton (fb@(x , fx＝y))
--       = (g y , fg y) =  (x , (transport () gy＝x  fg y))
--          -- singletons-are-subsingletons _
--          --  (retract-of-singleton fiber-is-singleton-Σ-retract
--          --     (singleton-types-are-singletons _ (g y)))
--          --  (g y , fg y)
--          --  fb

--     proof : Σ c ∶ (fiber f y) , is-center _ c
--     proof = (g y , fg y) , fiber-is-singleton


-- corollaries
-- inverses-are-equivs : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) (e : is-equiv f)
--                     → is-equiv (inverse f e)
-- inverses-are-equivs = {!!}

{-
  univalence
-}

quasi-equiv : (A : Set ℓ) (B : Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
quasi-equiv A B = Σ f ∶ (A → B) , invertible f

Id→Eq : (X Y : Set ℓ) → X ＝ Y → X ≃ Y
Id→Eq X X (refl X) = refl≃ X

is-univalent : (ℓ : Level) → Set (lsuc ℓ)
is-univalent ℓ = ∀ (X Y : Set ℓ) → is-equiv (Id→Eq X Y)

univalence-≃ : is-univalent ℓ → (X Y : Set ℓ) → (X ＝ Y) ≃ (X ≃ Y)
univalence-≃ ua X Y = Id→Eq X Y , ua X Y

Eq→Id : is-univalent ℓ → (X Y : Set ℓ) → X ≃ Y → X ＝ Y
Eq→Id ua X Y = inverse (Id→Eq X Y) (ua X Y)

Id→fun : {X Y : Set ℓ} → X ＝ Y → X → Y
Id→fun {ℓ} {X} {Y} p = equiv-fn (Id→Eq X Y p)
