{-
  first order logic
-}

id : {A : Set} → A → A
id a = a

_◦_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ◦ h = λ x → g (h x)

-- top type (true)
data ⊤ : Set where
  ⟨⟩ : ⊤

-- bottom type (false)
data ⊥ : Set where

absurd : {A : Set} → ⊥ → A
absurd ()

-- product (AND)
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

fst : {A B : Set} → A × B → A
fst (x , y) = x

snd : {A B : Set} → A × B → B
snd (x , y) = y

-- coproduct (OR)
data _＋_ (A B : Set) : Set where
  left  : A → A ＋ B
  right : B → A ＋ B

case : {A B C : Set} → (A ＋ B) → (A → C) → (B → C) → C
case (left a)  ac bc = ac a
case (right b) ac bc = bc b

-- double negation translation
lem : {P : Set} -> ((P ＋ (P → ⊥)) → ⊥) → ⊥
lem f = f (right (λ p → f (left p)))

-- dependent product (there exists)
data ∑ (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) → B x → ∑ A B

dfst : {A : Set} {B : A → Set} → ∑ A B → A
dfst (x , y) = x

dsnd : {A : Set} {B : A → Set} → (z : ∑ A B) → B (dfst z)
dsnd (x , y) = y

-- equality (equality)
data _≡_ {n : Agda.Primitive.Level} {A : Set n} : A → A → Set n where
  refl : {x : A} → x ≡ x

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

ap : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

subst : {A : Set} {x y : A} (C : A → Set) → x ≡ y → C x → C y
subst C refl cx = cx
