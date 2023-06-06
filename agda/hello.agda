{-# OPTIONS --without-K --exact-split --safe #-}

{-
  random proofs
-}

open import logic
open import eq
open import types

𝟚 = 𝟙 ＋ 𝟙
𝟚-ind : (A : 𝟚 → Set ℓ) → A (inl ⋆) → A (inr ⋆) → ((b : 𝟚) → A b)
𝟚-ind A a₀ a₁ = ＋-ind A
                (⊤-ind (λ (x : 𝟙) → (A (inl x))) a₀)
                (⊤-ind (λ (x : 𝟙) → (A (inr x))) a₁)

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

{-
  contradiction leads to bottom
-}

data Bad : ℕ → Set where
  badt : ⊤ → Bad 0
  badf : ⊥ → Bad 1

destroy : Bad 1 → ⊥
destroy (badf void) = void

negation : (0 ＝ 1) → ⊥
negation eq = destroy ((ȷ Bad eq) (badt ⋆))

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
[]        ++ bs = bs
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
map-id [] =
  begin
    map id [] =⟨⟩ []
  ∎
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
  begin
        map (f ∘ g) []
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
