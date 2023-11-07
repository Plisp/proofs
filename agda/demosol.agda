{-
  solutions to wednesday
-}

open import logic
open import paths
open import types
open import arith

--
-- Agda implements a constructive theory of mathematics
-- originally: BHK interpretation of intuitionistic logic/realizability
-- Brouwer, Heyting, Kolmogorov constructive proofs defined by induction:
--
-- a proof of P ∧ Q is a tuple (a,b) where a
-- a proof of P ∨ Q is a disjoint sum (0,a) or (1,b)
-- a proof of P → Q is a mathematical function mapping proofs of P to proofs of Q
-- ∃x.P(x) is a pair (x, a) where a is a proof of P(x)
-- ∀x.P(x) is a function converting x into proofs of P(x)
-- ¬P is P → ⊥ where ⊥ is a formula with no proofs
--
-- this predates the well-known "Curry-Howard isomorphism", which only
-- specifically applies to simply typed lambda calculus and the positive fragment
-- of intuitionistic logic... it's never really an isomorphism in general
--
-- Nowadays people refer to this principle of interpreting logic computationally
-- by "propositions as types".
-- Martin Lof elaborates a well known type theory (MLTT) upon which Agda's UTT
-- is based: this gives the first adequate computational foundation for most of
-- mathematics (non-logical inductive types) and this is still studied today
-- also see his excellent paper: constructive mathematics and computer programming
--
-- logical facts are interpreted internally as types: there is no distinction
-- between internal functions and implication: this is somewhat conceptually
-- cumbersome (exE vs meta_spec) in HOL, especially Isabelle
--
-- Let's see how this works: logic.agda
--
-- types, rather than being collections of individual elements are more
-- like math "structures" or "spaces", consisting of mapping in/out morphisms
-- describing its relationships to other types - it turns out this way you don't
-- need any notion of infinite set to get induction principles (initiality!!)
-- Just use universal properties! (e.g. we use adjoint equations without covectors)
-- (yes, types can be modelled by categories e.g. enriched CCCs)
--
-- another view: types are very weak sets of equations which allow many models
--
-- e.g. equality (＝) is defined as an *inductive family* of types, indexed by a
-- value of a certain type (a =ₙ a), allows taking a section by subst (simplified)
-- But it was found that not all proofs of equality could be proved equal
-- internally! (Hoffman's groupoid model refutes axiom K) What could this mean!!?
-- enter Homotopy Type Theory: interpret terms as points, types as spaces
-- equality as homotopy (family of maps from A->B indexed by [0,1] between f,g)
-- In the case of points: * |-> a/b where h₀ = f, h₁ = g
-- Equivalence between types becomes equality: isomorphism is truly substitutible
-- and can be used as transport for theorems proven about e.g. Peano -> bit numbers
-- These equalities are nontrivial! the transport isomorphism matters: bool -> bool
--
-- test : {X : Set} {x : X} → (p : x ＝ x) → refl x ＝ p -- without-K
-- test (refl x) = ? -- (not all equalities are trivial, programs are different)
--
-- the whole system has a model in some weird category/space, e.g. simplicial sets
-- Generally this will be more complicated than sets, but the foundation within
-- the system itself becomes much more intuitive - no representation, the tools
-- of functional programming (pattern-matching, higher-order theorems)
-- can be used for abstraction
-- e.g. proving ac rules uniformly over all binary operators and base types
-- e.g. expressing the Event type of itrees in a GADT-like way
--
-- finally, difficult programs can be specified clearly via their types, allowing
-- some very complex programs to be written correctly: https://ipqcoq.github.io/
-- the correct code can be extracted (although this should really be verified)
--
-- in my (evolving) opinion, something akin to types is most intuitive/simple
--

{-
  we begin with some builtin types: dependent functions, and naturals (jk I defined)

  note: type theory has good normalization properties: refl embeds all "simps"
  and its typechecking (normal evaluation required for indices) always terminates.
  This is crucial to consistency, otherwise ⊥ can be proved internally uh oh.

  Downside: equality reflection in ETT breaks type-safe normalization in binders
    Γ |- A ＝ B (prop equality)               check: λ x:⊥ . x y  vs  λ x:⊥ . T
    -----------
    Γ |- A ≡ B (computational equality)

  All proofs are manual in intensional type theory.

  another important property is canonicity: every closed term (not under a function)
  will compute to a constructor shape, justifying the induction principles and
  ensuring computation produces closed values of the expected form.
  Adding axioms e.g. funext breaks this immediately

  note: in my understanding, agda is a pedagogical type theory and simple
  experimental testbed for new type extensions, so not much automation.
  Proofs are first mostly guided by hand

  Coq is type theory-based with tactics, these can always be builtin externally.
  Significant use of a verified computation is possible: 4-color theorem Coq

-}

fact-iter : ℕ → ℕ → ℕ
fact-iter zero    acc = acc
fact-iter (suc n) acc = fact-iter n (suc n * acc)

factorial : ℕ → ℕ
factorial n = fact-iter n 1

-- C-c c-c for case split on n
-- C-c c-a for filling equalities
fact-commut-mult : (n k acc : ℕ) → fact-iter n (k * acc) ＝ k * fact-iter n acc
fact-commut-mult zero    k acc = refl _
fact-commut-mult (suc n) k acc =
  begin                                     fact-iter (suc n) (k * acc)
    =⟨⟩                                     fact-iter n (suc n * (k * acc))
    =⟨ ap (λ e → fact-iter n e) (left-ac-* (suc n) k acc) ⟩ -- see op.agda
                                            fact-iter n (k * (suc n * acc))
    =⟨ fact-commut-mult n k (suc n * acc) ⟩ k * fact-iter n (suc n * acc)
    =⟨⟩                                     k * fact-iter (suc n) acc
  ∎

fact-lemma : (n acc : ℕ) → fact-iter (suc n) acc ＝ suc n * fact-iter n acc
fact-lemma zero    acc = refl _
fact-lemma (suc n) acc =
  begin                                   fact-iter (suc (suc n)) acc
    =⟨⟩                                   fact-iter (suc n) ((suc (suc n)) * acc)
    =⟨ fact-lemma n (suc (suc n) * acc) ⟩ suc n * fact-iter n (suc (suc n) * acc)
    =⟨ ap (λ e → suc n * e) (fact-commut-mult n (suc (suc n)) acc) ⟩
                                          suc n * (suc (suc n) * fact-iter n acc)
    =⟨ left-ac-* (suc n) (suc (suc n)) (fact-iter n acc) ⟩
                                          suc (suc n) * (suc n * fact-iter n acc)
    =⟨ ap (λ e → suc (suc n) * e) (sym＝ (fact-lemma n acc)) ⟩
                                          suc (suc n) * fact-iter (suc n) acc
  ∎

factorial-rec : (n : ℕ) → factorial (suc n) ＝ (suc n) * factorial n
factorial-rec zero    = refl _
factorial-rec (suc n) = fact-lemma (suc n) 1

{-
  fib
-}

-- *0* 1 1 *2* 3 5 *8* 13 21 *34* ...
fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc a)) = fib a + fib (suc a)

mutual
  -- an inductive predicate: a piece of DATA containing nested proofs
  data even : ℕ → Set where -- type indexed over ℕ note: nothing said about even(1)
    ev0 : even 0
    evS : {n : ℕ} → odd n → even (suc n)

  data odd : ℕ → Set where
    oddS : {n : ℕ} → even n → odd (suc n)

  data tripl : ℕ → Set where
    t0 : tripl 0
    t0S : {n : ℕ} → trip2 n → tripl (suc n)

  data trip1 : ℕ → Set where
    t1S : {n : ℕ} → tripl n → trip1 (suc n)

  data trip2 : ℕ → Set where
    t2S : {n : ℕ} → trip1 n → trip2 (suc n)

-- even theorems: Zoltan avoided a lot of this base case duplication
-- see: https://gist.github.com/zaklogician/600666401a8df15afa2c05a879624d2a
evn-pred : {n : ℕ} → even (suc n) → odd n
evn-pred {0} (evS ()) -- 1 isn't even
evn-pred {suc n} (evS x) = x

odd-pred : {n : ℕ} → odd (suc n) → even n
odd-pred {0} (oddS ev0) = ev0
odd-pred {suc n} (oddS x) = x

odd+odd=even : {a b : ℕ} → odd a → odd b → even (a + b)
odd+odd=even {0} {b} ()
odd+odd=even {1} {b} oa ob = evS ob
odd+odd=even {suc (suc a)} {b} oSSa ob = evS (oddS (odd+odd=even oa ob))
  where
  oa : odd a
  oa = evn-pred (odd-pred oSSa)

odd+even=odd : {a b : ℕ} → odd a → even b → odd (a + b)
odd+even=odd {0} {b} ()
odd+even=odd {1} {b} oa eb = oddS eb
odd+even=odd {suc (suc a)} {b} oSSa eb =
  oddS (evS (odd+even=odd (evn-pred (odd-pred oSSa)) eb))

even+odd=odd : {a b : ℕ} → even a → odd b → odd (a + b)
even+odd=odd {a} {b} ea ob = -- transport?
  transport (λ x → odd x) (commutes-+ b a) (odd+even=odd {b} {a} ob ea)

-- trip theorems
tripl-pred : {n : ℕ} → tripl (suc n) → trip2 n
tripl-pred {0} (t0S ())
tripl-pred {1} (t0S (t2S ()))
tripl-pred {2} _ = t2S (t1S t0)
tripl-pred {suc (suc (suc n))} (t0S x) = x

trip1-pred : {n : ℕ} → trip1 (suc n) → tripl n
trip1-pred {0} p = t0
trip1-pred {1} (t1S (t0S ()))
trip1-pred {2} (t1S (t0S (t2S ())))
trip1-pred {suc (suc (suc n))} (t1S x) = x

trip2-pred : {n : ℕ} → trip2 (suc n) → trip1 n
trip2-pred {0} (t2S ())
trip2-pred {1} (t2S (t1S t0)) = t1S t0
trip2-pred {2} (t2S (t1S (t0S ())))
trip2-pred {suc (suc (suc n))} (t2S x) = x

-- proof of first direction
mutual
  tripl-fib-even : (n : ℕ) → tripl n → even (fib n)
  tripl-fib-even 0 _ = ev0
  tripl-fib-even 1 (t0S ())
  tripl-fib-even (suc (suc n)) pSSn =
    odd+odd=even (trip1-fib-odd n x) (trip2-fib-odd (suc n) y)
    where
    x : trip1 n
    x = trip2-pred (tripl-pred pSSn)
    y : trip2 (suc n)
    y = tripl-pred pSSn

  trip1-fib-odd : (n : ℕ) → trip1 n → odd (fib n)
  trip1-fib-odd 0 ()
  trip1-fib-odd 1 _ = oddS ev0
  trip1-fib-odd (suc (suc n)) pSSn =
    odd+even=odd (trip2-fib-odd n (tripl-pred (trip1-pred pSSn)))
                 (tripl-fib-even (suc n) (trip1-pred pSSn))

  trip2-fib-odd : (n : ℕ) → trip2 n → odd (fib n)
  trip2-fib-odd 0 ()
  trip2-fib-odd 1 _ = oddS ev0 -- fib 1 = 1
  trip2-fib-odd (suc (suc n)) pSSn =
    even+odd=odd (tripl-fib-even n (trip1-pred (trip2-pred pSSn)))
                 (trip1-fib-odd (suc n) (trip2-pred pSSn))

-- deriving the contradiction
all-trip : ∀ n → tripl n ＋ trip1 n ＋ trip2 n
all-trip 0 = inl t0
all-trip (suc n) with (all-trip n)
...              | inl r0 = inr (inl (t1S r0))
...              | inr (inl r1) = inr (inr (t2S r1))
...              | inr (inr r2) = inl (t0S r2)

not-tripl-odd : ∀ n → ¬ tripl n → odd (fib n)
not-tripl-odd n = trip12-fib-odd ∘ (not-tripl-trip12 n)
  where
  trip12-fib-odd : ∀ {n} → trip1 n ＋ trip2 n → odd (fib n)
  trip12-fib-odd {n} (inl t1) = trip1-fib-odd n t1
  trip12-fib-odd {n} (inr t2) = trip2-fib-odd n t2

  not-tripl-trip12 : ∀ n → ¬ tripl n → trip1 n ＋ trip2 n
  not-tripl-trip12 n p with (all-trip n)
  ...                  | inl t = rec⊥ _ (p t)
  ...                  | inr x = x

-- sneaky! this implies even decidable
odd-not-even : ∀ {n} → odd n → ¬ even n
odd-not-even {0} ()
odd-not-even {suc n} (oddS en) (evS on) = odd-not-even on en

contrℕ : {A B : ℕ → Set}
       → (∀ n → B n ＋ ¬ B n)
       → (∀ n → ¬ B n → ¬ A n)
       → (∀ n → (A n → B n))
contrℕ {A} {B} lemb contrab n an =
  rec＋ (B n) (λ bn → bn) (λ nbn → rec⊥ (B n) (contrab n nbn an)) (lemb n)

Lem = (P : ℕ → Set) → ∀ n → (P n) ＋ ¬ (P n)

even-triples-only0 : Lem → ∀ n → even (fib n) → tripl n
even-triples-only0 lem = contrℕ (lem tripl) (λ n → odd-not-even ∘ not-tripl-odd n)

{-
  constructive proof
-}

contravariance : {A B : Set} → (A → B) → (¬ B → ¬ A)
contravariance ab nb = nb ∘ ab

contradiction : {A B : Set} → (B ＋ ¬ B) → (¬ B → ¬ A) → (A → B)
contradiction (inl b) nba a = b
contradiction {A}{B} (inr nb) nb→na a = rec⊥ B ((nb→na nb) a)

mutual
  trip1-not-trip : ∀ {n} → trip1 n → ¬ tripl n
  trip1-not-trip {0} ()
  trip1-not-trip {suc n} (t1S r0) (t0S r2) = trip2-not-trip r2 r0

  trip2-not-trip : ∀ {n} → trip2 n → ¬ tripl n
  trip2-not-trip {0} ()
  trip2-not-trip {1} (t2S ())
  trip2-not-trip {suc (suc n)} (t2S (t1S r0)) (t0S (t2S r1))
    = trip1-not-trip r1 r0

tripl-decidable : ∀ n → tripl n ＋ ¬ tripl n
tripl-decidable n with (all-trip n)
...               | inl r0 = inl r0
...               | inr (inl r1) = inr (trip1-not-trip r1)
...               | inr (inr r2) = inr (trip2-not-trip r2)

even-triples-only : ∀ n → even (fib n) → tripl n
even-triples-only = contrℕ tripl-decidable (λ n → odd-not-even ∘ not-tripl-odd n)

{-
  (constructive) choice - there exists a more usual version on prop-truncation
-}

open import Agda.Primitive
open import hott

choice-theorem : (X : Set ℓ) (A : X → Set ℓ₁) -- for every indexed family A
               → (R : (x : X) → A x → Set ℓ₂)
               → ((x : X) → Σ a ∶ A x , R x a) -- already contains the witness
               → Σ f ∶ Π A , ((x : X) → R x (f x)) -- choose one for each index
choice-theorem X A R s = (λ x → pr₁ (s x)) , (λ x → pr₂ (s x))
