(*
 * Coinductive semantics with interaction trees!
 *
 * Directly express an infinite tree program-semantics structure via continuations.
 * By developing an algebra, reasoning can be mostly done above the Tau level,
 * which are convenient for expressing silent program steps which may differ,
 * depending on context.
 *
 * In comparision to the clock approach in cakeML's FBS semantics, there is less
 * distinction between finite/infinite programs, which allows local reasoning.
 * Oracle queries are encoded by events, and 'evaluating' in a context where the
 * responses are limited, we can simulate interaction with the external world.
 * Although that possibility depends on the granularity of restrictions on results.
 *
 * specifications should be *structural*, proofs should be *syntax-directed*
 *
 * One promising approach:
 * 1. express a clear (tauless) decomposition of the spec w/ conditions on FFI
 * 2. prove equivalence to the actual program semantics via weak bisimulation
 *
 * future work: ideally we want some way of automatically unfolding/executing a
 * program, to easily show facts about its interaction tree directly. This should
 * also allow for automated removal of Tau nodes. Could this be easier with types?
 *
 * note: Since they are the greatest fixpoint, they may also encode recursive tree
 * types using appropriate event data - e.g. W-trees. *
 * note: programs/simps/rewrites getting stuck in general is hard to predict and
 * annoying, proving strong normalization is the way out/weak ad-hoc size measure
 * note: look into how to execute coinductive programs with progress?
 *)

open HolKernel boolLib bossLib BasicProvers;
open itreeTauTheory;

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
Overload bind[local] = “itree_bind”;
Overload iter[local] = “itree_iter”;

val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;

(* these are useful ONLY for bisimulation *)
val or1_tac = disj1_tac
val or2_tac = disj2_tac >> disj1_tac;
val or3_tac = disj2_tac >> disj2_tac;
val or4_tac = disj2_tac >> disj2_tac >> disj2_tac;

(*/ basic examples of itree definition
   itree_unfold f is the final (coinductive) arrow to the capital algebra
   where f = structure map (into primed itree), seed = itree algebra instance
 *)

Theorem spin_unfold[simp]:
  Tau spin = spin
Proof
  rw[spin, Once itree_unfold]
QED

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
  echo = Vis Input (λ n. Vis (Output n) (λ x. echo))
Proof
  rw[echo,       Once itree_unfold] >>
  rw[FUN_EQ_THM, Once itree_unfold]
QED

(*/ misc abstract nonsense
   just to have a richer equational theory for wbisim
 *)

Theorem itree_bind_emit:
  bind (emit e) k = Vis e k
Proof
  rw[itree_trigger_def, itree_bind_thm, FUN_EQ_THM]
QED

Theorem itree_bind_ret_inv:
  bind t k = Ret r ⇒ ∃r'. t = Ret r' ∧ Ret r = (k r')
Proof
  Cases_on ‘t’ >> fs[itree_bind_thm]
QED

Theorem itree_wbisim_vis:
  ∀e k1 k2. (∀r. k1 r ≈ k2 r) ⇒ Vis e k1 ≈ Vis e k2
Proof
  metis_tac[strip_tau_cases, itree_wbisim_cases]
QED

(*/
  coinduction
 *)

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

Theorem spin_inf:
  itree_inf spin
Proof
  irule itree_inf_coind >>
  qexists_tac ‘λt. t = (Tau t)’ >>
  metis_tac[spin_unfold]
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

open arithmeticTheory;
open stringLib;

Definition iterate_def:
  iterate emit succ zero =
  itree_unfold (λs'. Vis' (emit s') (λ_. (succ s'))) zero
End

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
  ‘EVEN (n+1+1) ⇔ EVEN (n+2)’ suffices_by metis_tac[EVEN, SUC_ONE_ADD, ADD_SYM] >>
  rw[]
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
  even_spec 0 = bind (bind (emit "even")
                     (λ_. (emit "odd")))
                  (λ_. even_spec 0)
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

(* open ASCIInumbersTheory; *)

Definition even_prog_def:
  even_prog =
  Vis "hi, input nuber:"
      (λk. iter (λs. Vis (if EVEN s then "even" else "odd") (λ_. Ret (INL (s+1))))
                k)
End

(* even is a constraint on event responses *)
(* should use do notation later for clarity *)
(* Theorem even_prog_spec: *)
(*   ∃prelude loop coda. even_prog = bind (bind prelude loop) coda *)
(*   ∧ prelude = emit "hi, input nuber:" *)
(*   ∧ EVEN k ⇒ loop k ≈ (if (k = 100) *)
(*                        then (Ret r) *)
(*                        else (Vis "even" (λ_. Vis "odd" (λ_. loop k)))) *)
(*   ∧ coda r = emit (CONCAT [(n2s r) , "bye"]) *)
(* Proof *)
(*   cheat *)
(* QED *)
