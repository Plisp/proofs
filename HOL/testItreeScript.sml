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

open HolKernel boolLib bossLib BasicProvers; (* recommended by Magnus *)
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
   itree_unfold f is the final (coinductive) arrow to the capital algebra
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

(*/ misc abstract nonsense
   just to have a richer equational theory for wbisim
 *)

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

(*/ coinduction
   for greater structural variation
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

















open panItreeSemTheory;

(*/ equational theorems for mrec
   mrec expresses a recursive computation by iterating Vis INL

   iiter (Ret INL) → Tau (itree_unfold (iiter_cb (mrec_cb h_prog))
                              (mrec_cb h_prog (bind (rh state_res) k))) to continue
   mrec: Vis (INL (prog × newstate)) k → Ret (INL (h_prog prog bind k))
   mrec: Vis (INR (svis_ev × result->itree)) k → Ret (INL (h_prog prog bind k))
 *)

Theorem mrec_iter_body_thm[simp]:
  iter (mrec_iter_body rh) (Ret x) = Ret x ∧
  iter (mrec_iter_body rh) (Tau t) = Tau (iter (mrec_iter_body rh) t) ∧
  iter (mrec_iter_body rh) (Vis (INL s) g)
  = Tau (iter (mrec_iter_body rh) (rh s >>= g)) ∧
  iter (mrec_iter_body rh) (Vis (INR e) k)
  = Vis e (λx. Tau (iter (mrec_iter_body rh) (k x)))
Proof
  rw[Once itree_iter_thm, mrec_iter_body_def] >>
  rw[Once itree_iter_thm, mrec_iter_body_def]
QED

Theorem mrec_iter_ret_inv:
  mrec_iter_body rh t = Ret (INR r) ⇒ t = (Ret r)
Proof
  rw[mrec_iter_body_def] >>
  Cases_on ‘t’ >> fs[] >-
   (Cases_on ‘a’ >> fs[])
QED

Definition itree_mrec_def:
  itree_mrec rh seed =
  itree_iter (mrec_iter_body rh) (rh seed)
End

(* mrec iterates sequentially on its seed *)
Theorem itree_mrec_bind:
  iter (mrec_iter_body rh) (t >>= k) =
  (iter (mrec_iter_body rh) t) >>= (λx. iter (mrec_iter_body rh) (k x))
Proof
  rw[Once itree_strong_bisimulation] >>
  qexists_tac ‘λa b. ∃ps. a = iter (mrec_iter_body rh) (ps >>= k) ∧
                          b = (iter (mrec_iter_body rh) ps)
                              >>= (λx. iter (mrec_iter_body rh) (k x))’ >>
  rw[] >-
   (metis_tac[]) >-
   (‘mrec_iter_body rh (ps >>= k)
     >>= (λx. case x of INL a => Tau (iter (mrec_iter_body rh) a) | INR b => Ret b)
     = Ret x’ by gvs[Once itree_iter_thm] >>
    qpat_x_assum ‘Ret x = iter _ _’ kall_tac >>
    drule itree_bind_ret_inv >> pop_assum kall_tac >> strip_tac >>
    Cases_on ‘r'’ >> gvs[] >>
    drule_then strip_assume_tac mrec_iter_ret_inv >>
    drule_then strip_assume_tac itree_bind_ret_inv >>
    rw[]) >-
   (Cases_on ‘ps’ >-
     (fs[] >> metis_tac[]) >-
     (fs[] >> metis_tac[]) >-
     (Cases_on ‘a’ >> fs[GSYM itree_bind_assoc] >> metis_tac[])) >-
   (Cases_on ‘ps’ >> fs[] >-
     (metis_tac[]) >-
     (Cases_on ‘a'’ >> fs[] >>
      strip_tac >> disj1_tac >>
      qexists_tac ‘Tau (g s)’ >>
      rw[]))
QED

(*/ pancake theorems
   syntax directed rewrites
 *)

Inductive leaf:
  (leaf r (Ret r)) ∧
  (leaf r t ⇒ leaf r (Tau t)) ∧
  (∀a. leaf r (f a) ⇒ leaf r (Vis e f))
End

Theorem seq_thm:
  itree_mrec h_prog (Seq p p2, s) =
  Tau (itree_mrec h_prog (p, s)
                  >>= (λ(res,s').
                         if res = NONE
                         then Tau (itree_mrec h_prog (p2, s'))
                         else (Ret (res, s'))))
Proof
  rw[itree_mrec_def] >>
  rw[h_prog_def, h_prog_seq_def] >>
  rw[itree_mrec_bind] >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  Cases_on ‘x’ >> rw[]
QED

(* Theorem seq_lift0: *)
(*   ∀p s. *)
(*   leaf (NONE, s') (itree_mrec h_prog (p, s)) ⇒ *)
(*   to_ffi (itree_mrec h_prog (Seq p p2, s)) *)
(*          ≈ (to_ffi (itree_mrec h_prog (p, s)) >>= *)
(*             (λ_. to_ffi (itree_mrec h_prog (p2, s')))) *)
(* Proof *)
(*   Induct_on ‘leaf’ >> *)
(*   rw[] >- *)
(*    (fs[seq_thm, itree_wbisim_refl]) >- *)
(*    (rename1 ‘to_ffi t >>= _’ >> *)
(*     rw[ξ] *)
(*    ) *)
(* QED *)

Definition revert_binding_def:
  revert_binding name old_s
  = (λ(res,s').
       Ret
       (res,
        s' with locals :=
        res_var s'.locals (name,FLOOKUP old_s.locals name)))
End

Theorem h_prog_dec_alt:
  h_prog_dec vname e p s =
  case eval (reclock s) e of
    NONE => Ret (SOME Error,s)
  | SOME value =>
      Vis (INL (p,s with locals := s.locals |+ (vname,value)))
          (revert_binding vname s)
Proof
  rw[h_prog_dec_def, revert_binding_def]
QED

(* f, f' type vars instantiated differently smh *)
(* relies on mrec_cb h_prog rev -> only Ret INR, so can't prolong iteration *)
Theorem itree_mrec_bind_ret:
  ∀f f'.
    (∀a. ∃r. (f a) = (Ret r) ∧ (f' a) = (Ret r)) ⇒
    ∀t. iter (mrec_iter_body h_prog) (t >>= f)
        = (iter (mrec_iter_body h_prog) t) >>= f'
Proof
  rpt strip_tac >>
  rw[itree_mrec_bind] >>
  AP_TERM_TAC >> rw[FUN_EQ_THM] >>
  pop_assum $ qspec_then ‘x’ strip_assume_tac >> fs[]
QED

Theorem dec_thm:
  (eval (reclock s) e = SOME k) ⇒
  (itree_mrec h_prog (Dec name e p,s))
  = Tau (itree_mrec h_prog (p,s with locals := s.locals |+ (name,k))
      >>= (revert_binding name s))
Proof
  rw[itree_mrec_def] >>
  rw[h_prog_def, h_prog_dec_def] >>
  rw[GSYM revert_binding_def] >>
  irule itree_mrec_bind_ret >>
  rw[revert_binding_def] >>
  Cases_on ‘a’ >> rw[]
QED

(*/ massaging into FFItree
   fix merged!
 *)

Theorem to_stree_simps[simp]:
  to_stree ((Ret x) : (β, α) mtree) = Ret x ∧
  to_stree ((Tau t) : (β, α) mtree) = Tau (to_stree t) ∧
  to_stree ((Vis eg k) : (β, α) mtree) = Vis (FST eg) (to_stree ∘ k ∘ SND eg)
Proof
  rw[to_stree_def] >>
  rw[Once itree_unfold] >>
  Cases_on ‘eg’ >> gvs[]
QED

Theorem to_stree_seq:
  to_stree t ≈ (Ret (SOME v, s))
  ⇒ to_stree
    (t >>= (λ(res,s'). if res = NONE then f NONE s' else Ret (res,s'))) ≈
    (Ret (SOME v, s))
Proof
  rw[Once itree_wbisim_cases] >>
  pop_assum mp_tac >> qid_spec_tac ‘t’ >>
  Induct_on ‘strip_tau’ >> rw[] >>
  gvs[Once $ DefnBase.one_line_ify NONE to_stree_simps, AllCaseEqs(),
      itree_wbisim_refl]
QED

Theorem pull_ffi_case[simp]:
  f (ffi_result_CASE ffi ret final) =
  ffi_result_CASE ffi (λ x y. f (ret x y)) (f ∘ final)
Proof
  Cases_on ‘ffi’ >> simp[]
QED







(*/ lifted versions
   not sure how to do seq? I guess internal lemmas are fine
*)

Theorem to_ffi_revert_bind:
  to_stree (t >>= revert_binding name s) = to_stree t
Proof
  cheat >>
  rw[Once itree_strong_bisimulation] >>
  qexists_tac ‘λa b. ∃t. a = to_stree (t >>= revert_binding name s) ∧
                         b = to_stree t’ >>
  rw[] >-
   (metis_tac[]) >-
   (Cases_on ‘t'’ >> fs[itree_bind_thm] >-
     (fs[revert_binding_def] >> Cases_on ‘x'’ >> fs[]) >- (* impossible *)
     (Cases_on ‘a’ >> fs[])) >-
   (Cases_on ‘t'’ >> fs[itree_bind_thm] >-
     (fs[revert_binding_def] >> Cases_on ‘x’ >> fs[]) >-
     (metis_tac[]) >-
     (Cases_on ‘a’ >> fs[])) >-
   (Cases_on ‘t'’ >> fs[itree_bind_thm] >-
     (fs[revert_binding_def] >> Cases_on ‘x’ >> fs[]) >>
    Cases_on ‘a'’ >> fs[] >>
    metis_tac[])
QED

Theorem dec_lifted:
  to_stree (itree_mrec h_prog (Dec name e p,s))
  = let res = eval (reclock s) e in
      if (res = NONE)
      then Ret ((SOME Error),s)
      else Tau (to_stree
                (itree_mrec h_prog
                            (p, s with locals := s.locals |+ (name,THE res))))
Proof
  rw[] >-
   (rw[itree_mrec_def, h_prog_def, h_prog_dec_def]) >-
   (Cases_on ‘eval (reclock s) e’ >> fs[] >>
    drule dec_thm >> rw[to_ffi_revert_bind])
QED



















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
