(*
 * Coinductive semantics with interaction trees!
 *
 * Directly express an infinite tree program-semantics structure via continuations.
 * By developing an algebra, reasoning can be mostly done above the Tau level,
 * which are convenient for expressing silent program steps which may differ
 * depending on context. Taus are necessary in the semantics, as termination of
 * of loops cannot determined ahead of time but we need productivity for soundness.
 * Oracle queries are encoded by events, and 'evaluating' in a context where the
 * responses are limited, we can simulate interaction with the external world.
 * Although that possibility depends on the granularity of restrictions on results.
 *
 * Itrees make the nondeterminism external to the structure: this is a better fit
 * for mix-and-match with sets of restrictions on interactions - device models -
 * rather than coding specific oracles.
 * In comparision to the clock approach in cakeML's FBS semantics, there is less
 * distinction between finite|infinite programs, usually allowing local reasoning.
 * Consider this an equivalent representation more suited to program reasoning, as
 * opposed to compiler correctness proofs.
 *
 * detail: fix_clock is necessary in proofs as with induction on e.g.(Seq p1 p2)
 * to prove productivity we need to adjust the clock of p2 to start from the
 * amount after running p1.
 *
 * specifications should be *structural*, in terms of observable interaction rather
 * than detailing implementation. but proofs should be *syntax-directed*
 *
 * One promising approach:
 * 1. express abstract HOL version of the program with conditions on FFI
 * 2. trim away invalid responses by the environment not covered by a proof
 * 3. prove equivalence to the trimmed program semantics via weak bisimulation
 * 4. prove properties of the abstraction, which then also proves the same thing?
 *    about the program semantics
 *
 * future work:
 * note: Since they are the greatest fixpoint, they may also encode recursive tree
 * types using appropriate event data - e.g. W-trees. *
 * note: programs|simps|rewrites getting stuck in general is hard to predict and
 * annoying, proving strong normalization is the way out|weak ad-hoc size measure
 * note: look into how to execute coinductive programs with progress?
 *)

open stringLib; (* parsing, text examples etc. *)
open itreeTauTheory;

(* Theorem test: *)
(*   (∀x y. V(i(x,i(y,x)))) ∧ *)
(*   (∀x y z. V(i(i(x,i(y,z)), i(i(x,y),i(x,z))))) ∧ *)
(*   (∀x y. V(i(i(y,x),i(n(x),n(y))))) ∧ *)
(*   (∀x y. V(i(x,y)) ∧ V(x) ⇒ V(y)) *)
(*   ⇒ *)
(*   V(i(a,i(i(a,b),b))) *)
(* Proof *)
(*   metis_tac[] *)
(* QED *)

(* open monadsyntax; *)
(* val _ = *)
(*     monadsyntax.declare_monad ( *)
(*       "itree_monad", *)
(*       { bind = “itree_bind”, ignorebind = NONE, unit = “Ret”, *)
(*         guard = NONE, choice = NONE, fail = NONE} *)
(*     ) *)
(* val _ = monadsyntax.temp_enable_monad "itree_monad"; *)

Definition itree_trigger_def:
  itree_trigger event = Vis event Ret
End
Overload emit[local] = “itree_trigger”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>="[local] = “itree_bind”;
Overload iter[local] = “itree_iter”;

val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;

(* these are useful ONLY for bisimulation *)
val or1_tac = disj1_tac
val or2_tac = disj2_tac >> disj1_tac;
val or3_tac = disj2_tac >> disj2_tac;

(*/ basic examples of itree definition
   itree_unfold f is the final (coinductive) arrow to the final coalgebra
   where f = structure map (into primed itree), seed = itree algebra instance
 *)

(* echo taken from paper, a bit different with HOL unfold vs deptypes *)
(* note: response types can't be restricted per event type *)
Datatype:
  IO = Input | Output num
End

Definition echo:
  echo = itree_unfold (λ s. case s of
                            | Input    => Vis' Input      (λ n. Output n)
                            | Output n => Vis' (Output n) (λ v. Input))
                      Input
End

Theorem echo_unfold:
  echo = Vis Input (λ n. Vis (Output n) (λ_. echo))
Proof
  rw[echo,       Once itree_unfold] >>
  rw[FUN_EQ_THM, Once itree_unfold]
QED

(* simple stuff *)

Theorem itree_bind_emit:
  (emit e) >>= k = Vis e k
Proof
  rw[itree_trigger_def, itree_bind_thm, FUN_EQ_THM]
QED

Theorem itree_bind_tau_inv:
  t >>= k = Tau s ∧ (¬∃r. t = Ret r) ⇒ ∃s'. t = Tau s' ∧ s' >>= k = s
Proof
  Cases_on ‘t’ >> fs[itree_bind_thm]
QED

Theorem itree_bind_vis_inv:
  t >>= cont = Vis e k ∧ (¬∃r. t = Ret r)
  ⇒ ∃k'. t = Vis e k' ∧ ∀x. (k' x) >>= cont = k x
Proof
  Cases_on ‘t’ >> fs[itree_bind_thm] >>
  rw[FUN_EQ_THM]
QED

Theorem itree_wbisim_vis:
  ∀e k1 k2. (∀r. k1 r ≈ k2 r) ⇒ Vis e k1 ≈ Vis e k2
Proof
  metis_tac[strip_tau_cases, itree_wbisim_cases]
QED

val vis_tac = irule itree_wbisim_vis >> Cases;

(* finite on all paths: generates backwards coind & forwards cases *)
CoInductive itree_fin:
  (∀t. itree_fin t ⇒ itree_fin (Tau t)) ∧
  (∀e k. (∀r. itree_fin (k r)) ⇒ itree_fin (Vis e k)) ∧
  (∀r. itree_fin (Ret r))
End

(* infinite on all paths *)
CoInductive itree_inf:
  (∀t. itree_inf t ⇒ itree_inf (Tau t)) ∧
  (∀e k. (∀r. itree_inf (k r)) ⇒ itree_inf (Vis e k))
End

Theorem ret_fin:
  itree_fin (Tau (Ret r))
Proof
  rw[Once itree_fin_cases] >>
  rw[Once itree_fin_cases]
QED

Definition vis_spin_def:
  vis_spin = itree_unfold (λs. Vis' s I) 0
End

Theorem vis_spin_inf:
  itree_inf vis_spin
Proof
  irule itree_inf_coind >>
  qexists_tac ‘λt. ∃k. t = Vis k (itree_unfold (λs. Vis' s I))’ >>
  rw[vis_spin_def] >>
  rw[Once itree_unfold]
QED

(* looping vis nodes *)

Definition iterate_def:
  iterate emit succ zero =
  itree_unfold (λs'. Vis' (emit s') (λ_. (succ s'))) zero
End

(*/ recursive specifications
   testing
 *)

open arithmeticTheory;

Definition even_spec_def:
  even_spec k = iterate (λx. if EVEN x then "even" else "odd") (λn. 1 + n) k
End

Theorem even_add1:
  EVEN k ⇔ ¬EVEN (k+1)
Proof
  metis_tac[EVEN, SUC_ONE_ADD, ADD_SYM]
QED

(* backwards extensionality *)
Theorem even_spec_unfold:
  ∀k. EVEN k ⇒ even_spec k = Vis "even" (λ_. Vis "odd" (λ_. even_spec (2 + k)))
Proof
  rw[even_spec_def] >>
  CONV_TAC $ LHS_CONV $ REWRITE_CONV[iterate_def] >>
  rw[itree_unfold] >>
  rw[combinTheory.o_DEF] >>
  rw[FUN_EQ_THM] >>
  rw[itree_unfold] >-
   (metis_tac[even_add1]) >-
   (rw[combinTheory.o_DEF] >>
    rw[iterate_def])
QED

Theorem even_add2:
  EVEN (n+2) ⇔ EVEN n
Proof
  rw[EVEN_ADD]
QED

Theorem even_spec_plus2:
  ∀k. even_spec (2+k) = even_spec k
Proof
  strip_tac >>
  qspecl_then [‘even_spec (2+k)’, ‘even_spec k’]
              strip_assume_tac itree_bisimulation >>
  fs[EQ_IMP_THM] >>
  pop_assum irule >>
  pop_assum kall_tac >>
  qexists_tac ‘λa b. ∃n. a = even_spec (2+n) ∧ b = even_spec n’ >>
  rw[] >> gvs[even_spec_def, iterate_def, Once itree_unfold] >-
   (qexists_tac ‘k’ >>
    simp[] >>
    CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV[itree_unfold] >>
    rw[]) >-
   (simp[Once itree_unfold] >>
    CONJ_TAC >-
     (rw[Once even_add2]) >-
     (qexists_tac ‘n+1’ >> rw[]))
QED

Theorem even_spec_thm:
  even_spec 0 = (emit "even" >>= (λ_. (emit "odd")))
              >>= (λ_. even_spec 0)
Proof
  rw[Once even_spec_unfold] >>
  rw[itree_bind_emit] >>
  rw[itree_bind_thm] >>
  rw[FUN_EQ_THM] >>
  rw[itree_bind_emit] >>
  rw[FUN_EQ_THM] >>
  qspec_then ‘0’ mp_tac even_spec_plus2 >>
  rw[]
QED
