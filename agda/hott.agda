{-# OPTIONS --without-K --exact-split --safe #-}


{-
  univalent math, hott chapter 3
-}

open import Agda.Primitive
open import logic
open import types
open import eq

{-
  -1-type
-}

is-center : (X : Set ℓ) → X → Set ℓ
is-center X c = (x : X) → c ＝ x

is-singleton : Set ℓ → Set ℓ
is-singleton X = Σ c ∶ X , is-center X c

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , ind⊤ (λ x → ⋆ ＝ x) (refl ⋆)

center : (X : Set ℓ) → is-singleton X → X
center X (c , p) = c

centerality : (X : Set ℓ) (i : is-singleton X) → (x : X) → center X i ＝ x
centerality X (c , p) = p

singleton-type : {X : Set ℓ} → X → Set ℓ
singleton-type {ℓ} {X} x = Σ y ∶ X , y ＝ x

singleton-type-center : {X : Set ℓ} (x : X) → singleton-type x
singleton-type-center x = (x , refl x)

singleton-type-centered : {X : Set ℓ} (x : X) (σ : singleton-type x)
                        → singleton-type-center x ＝ σ
singleton-type-centered x (x , refl x) = refl (x , refl x)

singleton-types-are-singletons : (X : Set ℓ) (x : X) → is-singleton (singleton-type x)
singleton-types-are-singletons X x -- v is-singleton (fiber id x) ⇔ c, c ＝ (x,refl x)
  = singleton-type-center x , singleton-type-centered x

-- (subtype) singletons but maybe not inhabited
is-subsingleton : Set ℓ → Set ℓ
is-subsingleton X = (x y : X) → x ＝ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = ind⊥ (λ x → (x ＝ y)) x

is-prop = is-subsingleton

singleton→subsingleton : (X : Set ℓ) → is-singleton X → is-subsingleton X
singleton→subsingleton X (c , p) x y = sym＝ (p x) ∙ p y

pointed-subsingleton→singleton : (X : Set ℓ) → X
                               → is-subsingleton X → is-singleton X
pointed-subsingleton→singleton X x s = (x , s x)

{-
  n-types
-}

0-type : Set ℓ → Set ℓ
0-type X = (x y : X) → is-subsingleton (x ＝ y)

is-set = 0-type

1-type : Set ℓ → Set ℓ
1-type X = {x y : X} (p q : x ＝ y) → is-subsingleton (p ＝ q)

_is-of-hlevel_ : Set ℓ → ℕ → Set ℓ
X is-of-hlevel 0       = is-singleton X
X is-of-hlevel (suc n) = (x x' : X) → ((x ＝ x') is-of-hlevel n)

subsingleton→set : (X : Set ℓ) → is-subsingleton X → is-set X
subsingleton→set X ss = proof
  where
    g : {x : X} (y : X) → x ＝ y
    g {x} y = ss x y

    lemma : {x y y' : X} (r : y ＝ y') → (g y) ∙ r ＝ g y'
    lemma {x}{y} r = sym＝ (transportpq＝q∙p r (g y)) ∙ apd (g {x}) r

    proof : (x y : X) (p q : x ＝ y) → p ＝ q
    proof x y p q = lcancel∙ (g {x} x) p q (lemma p ∙ sym＝ (lemma q))

-- the levels are upper closed
hlevel-suc : (X : Set ℓ) (n : ℕ)
           → X is-of-hlevel n → X is-of-hlevel (suc n)
hlevel-suc X 0       = λ h → λ x y →
                         let k = singleton→subsingleton X h in
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
  retracts ? bookmark
-}

-- right inverse
has-section : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
has-section {ℓ}{ℓ₁} {X}{Y} f = Σ g ∶ (Y → X) , f ∘ g ~ id

-- retract
_◁_ : Set ℓ → Set ℓ₁ → Set (ℓ ⊔ ℓ₁)
X ◁ Y = Σ f ∶ (Y → X) , has-section f

retraction : {X : Set ℓ} {Y : Set ℓ₁} → X ◁ Y → (Y → X)
retraction (r , s , η) = r

section : {X : Set ℓ} {Y : Set ℓ₁} → X ◁ Y → (X → Y)
section (r , s , η) = s

is-retract : {X : Set ℓ} {Y : Set ℓ₁} → (p : X ◁ Y) → retraction p ∘ section p ~ id
is-retract (r , s , η) = η

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
LEM' ℓ = (X : Set ℓ) → is-subsingleton X → is-singleton X ＋ is-empty X

{-
  equivalence
-}

invertible : {A : Set ℓ} {B : Set ℓ₁} (f : A → B) → Set (ℓ ⊔ ℓ₁)
invertible {ℓ}{ℓ₁} {A}{B} f = Σ g ∶ (B → A) , g ∘ f ~ id × f ∘ g ~ id

quasi-equiv : (A : Set ℓ) (B : Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
quasi-equiv A B = Σ f ∶ (A → B) , invertible f

-- witness x, f x = y
fiber : {X :  Set ℓ} {Y : Set ℓ₁} (f : X → Y) → Y → Set (ℓ ⊔ ℓ₁)
fiber {ℓ}{ℓ₁} {X}{Y} f y = Σ x ∶ X , f x ＝ y

fiber-base : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
            → fiber f y → X
fiber-base (x , p) = x

fiber-identity : {X : Set ℓ} {Y : Set ℓ₁} {f : X → Y} {y : Y}
               → (w : fiber f y) → f (fiber-base w) ＝ y
fiber-identity (x , p) = p

-- the fibre (preimage) of all y : Y under f is unique (size 1)
is-equiv : {X : Set ℓ} {Y : Set ℓ₁} → (X → Y) → Set (ℓ ⊔ ℓ₁)
is-equiv {ℓ}{ℓ₁} {X}{Y} f = Π y ∶ Y , is-singleton (fiber f y)

-- inverses
inverse : {X : Set ℓ} {Y : Set ℓ₁} (f : X → Y) → is-equiv f → (Y → X)
inverse f e y = fiber-base (center (fiber f y) (e y))

-- equivalence
_≃_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
X ≃ Y = Σ f ∶ (X → Y) , is-equiv f
infix 5 _≃_

Eq→fun : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → X → Y
Eq→fun (f , i) = f

id-is-equiv : (X : Set ℓ) → is-equiv id
id-is-equiv = singleton-types-are-singletons

id≃ : (X : Set ℓ) → X ≃ X
id≃ X = id , id-is-equiv X

Id→Eq : (X Y : Set ℓ) → X ＝ Y → X ≃ Y
Id→Eq X X (refl X) = id≃ X

is-univalent : (ℓ : Level) → Set (lsuc ℓ)
is-univalent ℓ = ∀ (X Y : Set ℓ) → is-equiv (Id→Eq X Y)

univalence-≃ : is-univalent ℓ → (X Y : Set ℓ) → (X ＝ Y) ≃ (X ≃ Y)
univalence-≃ ua X Y = Id→Eq X Y , ua X Y

Eq→Id : is-univalent ℓ → (X Y : Set ℓ) → X ≃ Y → X ＝ Y
Eq→Id ua X Y = inverse (Id→Eq X Y) (ua X Y)

Id→fun : {X Y : Set ℓ} → X ＝ Y → X → Y
Id→fun {ℓ} {X} {Y} p = Eq→fun (Id→Eq X Y p)
