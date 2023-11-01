(*
 * Coinductive semantics with interaction trees!
 *
 * Directly express an infinite tree program-semantics structure via continuations.
 * By developing an algebra, reasoning can be mostly done above the Tau level,
 * which are convenient for expressing silent program steps which may differ,
 * depending on context.
 *
 * In comparision to the clock approach in cakeML's FBS semantics, there is less
 * distinction between finite|infinite programs, which allows local reasoning.
 * Oracle queries are encoded by events, and 'evaluating' in a context where the
 * responses are limited, we can simulate interaction with the external world.
 * Although that possibility depends on the granularity of restrictions on results.
 *
 * specifications should be *structural*, proofs should be *syntax-directed*
 *
 * One promising approach:
 * 1. express a clear (tauless) decomposition of the spec with conditions on FFI
 * 2. prove equivalence to the actual program semantics via weak bisimulation
 *
 * future work: ideally we want some way of automatically unfolding|executing a
 * program, to easily show facts about its interaction tree directly. This should
 * also allow for automated removal of Tau nodes. Could this be easier with types?
 *
 * note: Since they are the greatest fixpoint, they may also encode recursive tree
 * types using appropriate event data - e.g. W-trees. *
 * note: programs|simps|rewrites getting stuck in general is hard to predict and
 * annoying, proving strong normalization is the way out|weak ad-hoc size measure
 * note: look into how to execute coinductive programs with progress?
 *)

open HolKernel boolLib bossLib BasicProvers; (* recommended by Magnus *)
open stringLib; (* parsing, text examples etc. *)
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
 *)

(* iiter (Ret INL) → Tau (itree_unfold (iiter_cb (mrec_cb h_prog))
                           (mrec_cb h_prog (bind (rh state_res) k))) to continue *)
(* mrec: Vis (INL (prog × newstate)) k → Ret (INL (h_prog prog bind k)) *)
(* mrec: Vis (INR (svis_ev × result->itree)) k → Ret (INL (h_prog prog bind k)) *)
Definition mrec_cb_def[simp]:
    mrec_cb rh (Ret r) = Ret (INR r)
  ∧ mrec_cb rh (Tau t) = Ret (INL t)
  ∧ mrec_cb rh (Vis (INL state_res) k) = Ret (INL (bind (rh state_res) k))
  ∧ mrec_cb rh (Vis (INR   ffi_res) k) = Vis ffi_res (λx. Ret (INL (k x)))
End

Theorem itree_mrec_alt:
  itree_mrec rh seed = iter (mrec_cb rh) (rh seed)
Proof
  rw[itree_mrec_def] >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE mrec_cb_def, combinTheory.o_DEF]
QED

Theorem iter_mrec_cb_thm[simp]:
  iter (mrec_cb rh) (Ret x) = Ret x ∧
  iter (mrec_cb rh) (Tau t) = Tau (iter (mrec_cb rh) t) ∧
  iter (mrec_cb rh) (Vis (INL s) g) = Tau (iter (mrec_cb rh) (bind (rh s) g)) ∧
  iter (mrec_cb rh) (Vis (INR e) k) = Vis e (λx. Tau (iter (mrec_cb rh) (k x)))
Proof
  rw[Once itree_iter_thm] >> rw[Once itree_iter_thm]
QED

Theorem mrec_cb_ret_inv:
  mrec_cb rh t = Ret (INR r) ⇒ t = (Ret r)
Proof
  rw[DefnBase.one_line_ify NONE mrec_cb_def] >>
  Cases_on ‘t’ >> fs[] >-
   (Cases_on ‘a’ >> fs[])
QED

Theorem itree_bind_ret_inv:
  bind t k = Ret r ⇒ ∃r'. t = Ret r' ∧ Ret r = (k r')
Proof
  Cases_on ‘t’ >> fs[itree_bind_thm]
QED

(* mrec iterates sequentially on its seed *)
Theorem itree_mrec_bind:
  iter (mrec_cb rh) (bind t k) =
  bind (iter (mrec_cb rh) t) (λx. iter (mrec_cb rh) (k x))
Proof
  rw[Once itree_strong_bisimulation] >>
  qexists_tac ‘λa b. ∃ps. a = iter (mrec_cb rh) (bind ps k) ∧
                          b = bind (iter (mrec_cb rh) ps)
                                (λx. iter (mrec_cb rh) (k x))’ >>
  rw[] >-
   (metis_tac[]) >-
   (‘bind (mrec_cb rh (bind ps k))
       (λx. case x of INL a => Tau (iter (mrec_cb rh) a) | INR b => Ret b)
     = Ret x’
      by gvs[Once itree_iter_thm] >>
    qpat_x_assum ‘Ret x = iter _ _’ kall_tac >>
    drule itree_bind_ret_inv >> pop_assum kall_tac >> strip_tac >>
    Cases_on ‘r'’ >> gvs[] >>
    drule mrec_cb_ret_inv >> strip_tac >>
    drule itree_bind_ret_inv >> strip_tac >>
    fs[Once itree_iter_thm] >>
    fs[Once itree_iter_thm]) >-
   (Cases_on ‘ps’ >-
     (fs[] >> metis_tac[]) >-
     (fs[] >> metis_tac[]) >-
     (Cases_on ‘a’ >> fs[] >-
       (fs[GSYM itree_bind_assoc] >> metis_tac[]))) >-
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

Theorem seq_thm:
  itree_mrec h_prog (Seq p p2, s) =
  Tau (bind (itree_mrec h_prog (p, s))
            (λ(res,s').
               if res = NONE
               then Tau (itree_mrec h_prog (p2, s'))
               else (Ret (res, s'))))
Proof
  rw[itree_mrec_alt] >>
  rw[h_prog_def, h_prog_rule_seq_def] >>
  rw[itree_mrec_bind] >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  Cases_on ‘x’ >> rw[]
QED

Definition revert_binding_def:
  revert_binding name old_s
  = (λ(res,s').
       Ret
       (res,
        s' with locals :=
        res_var s'.locals (name,FLOOKUP old_s.locals name)))
End

Theorem h_prog_rule_dec_alt:
  h_prog_rule_dec vname e p s =
  case eval s e of
    NONE => Ret (SOME Error,s)
  | SOME value =>
      Vis (INL (p,s with locals := s.locals |+ (vname,value)))
          (revert_binding vname s)
Proof
  rw[h_prog_rule_dec_def, revert_binding_def]
QED

(* f, f' type vars instantiated differently smh *)
(* relies on mrec_cb h_prog rev -> only Ret INR, so can't prolong iteration *)
Theorem itree_mrec_bind_ret:
  ∀f f'.
    (∀a. ∃r. (f a) = (Ret r) ∧ (f' a) = (Ret r)) ⇒
    ∀t. iter (mrec_cb h_prog) (bind t f) = (bind (iter (mrec_cb h_prog) t) f')
Proof
  rpt strip_tac >>
  rw[itree_mrec_bind] >>
  AP_TERM_TAC >> rw[FUN_EQ_THM] >>
  pop_assum $ qspec_then ‘x’ strip_assume_tac >> fs[]
QED

Theorem dec_thm:
  (eval s e = SOME k) ⇒
  (itree_mrec h_prog (Dec name e p,s))
  = Tau (bind
         (itree_mrec h_prog (p,s with locals := s.locals |+ (name,k)))
         (revert_binding name s))
Proof
  rw[itree_mrec_alt] >>
  rw[h_prog_def, h_prog_rule_dec_def] >>
  rw[GSYM revert_binding_def] >>
  irule itree_mrec_bind_ret >>
  rw[revert_binding_def] >>
  Cases_on ‘a’ >> rw[]
QED

(*/ massaging into FFItree
   fix merged!
 *)

Definition massage_cb_def[simp]:
  massage_cb (Ret (res, s)) = Ret' res ∧
  massage_cb (Tau kt) = Tau' kt ∧
  massage_cb (Vis (svis_ev, scb) st) = Vis' svis_ev (λffi_res. st (scb ffi_res))
End

(* massage Ret type from (η x state) -> η *)
(* convert Vis (sem_vis_event x (FFI_result -> itree)) ((prog x state) -> %itree)
-> Vis sem_vis_event (FFI_result -> itree) *)
Definition to_ffi_def:
  to_ffi t = itree_unfold massage_cb t
End

Theorem to_ffi_alt[simp]:
  to_ffi (Tau t) = Tau (to_ffi t) ∧
  to_ffi (Ret (p,s)) = Ret p ∧
  to_ffi (Vis (svis_ev,scb) g) = Vis svis_ev (λffi_res. to_ffi (g (scb (ffi_res))))
Proof
  rw[to_ffi_def] >> rw[Once itree_unfold] >>
  rw[combinTheory.o_DEF]
QED

Theorem pull_ffi_case[simp]:
  (to_ffi
   (iter (mrec_cb h_prog)
         (f (case res of
               FFI_return new_ffi new_bytes => a new_ffi new_bytes
             | FFI_final outcome => b outcome))))
  =
  (case res of
     FFI_final outcome =>
       to_ffi (iter (mrec_cb h_prog) (f (b outcome)))
   | FFI_return new_ffi new_bytes =>
       to_ffi (iter (mrec_cb h_prog) (f (a new_ffi new_bytes))))
Proof
  rw[FUN_EQ_THM] >>
  Cases_on ‘res’ >> rw[]
QED

Theorem pull_ffi_case2[simp]:
  (to_ffi
   (f (case res of
         FFI_return new_ffi new_bytes => a new_ffi new_bytes
       | FFI_final outcome => b outcome)))
  =
  (case res of
     FFI_final outcome => to_ffi (f (b outcome))
   | FFI_return new_ffi new_bytes => to_ffi (f (a new_ffi new_bytes)))
Proof
  rw[FUN_EQ_THM] >>
  Cases_on ‘res’ >> rw[]
QED

(* TODO for while, this is kinda silly *)
Theorem pull_ffi_case3[simp]:
  iter (mrec_cb h_prog)
  (bind (f (case res of
              FFI_return new_ffi new_bytes => a new_ffi new_bytes
            | FFI_final outcome => b outcome))
        k)
  =
  case res of
    FFI_final outcome => iter (mrec_cb h_prog) (bind (f (b outcome)) k)
  | FFI_return new_ffi new_bytes => iter (mrec_cb h_prog)
                                                  (bind (f (a new_ffi new_bytes)) k)
Proof
  rw[FUN_EQ_THM] >>
  Cases_on ‘res’ >> rw[]
QED

Theorem itree_evaluate_alt:
  itree_evaluate p s = to_ffi (itree_mrec h_prog (p,s))
Proof
  rw[itree_evaluate_def, sem_outer, to_ffi_def] >>
  AP_THM_TAC >> (* same fn => same on same arg, backwards *)
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE massage_cb_def, combinTheory.o_DEF]
QED

(*/ while
   ??
 *)
Definition h_prog_whilebody_cb_def[simp]:
    h_prog_whilebody_cb p (SOME Break) s' = Ret (INR (NONE,s'))
  ∧ h_prog_whilebody_cb p (SOME Continue) s' = Ret (INL (p,s'))
  ∧ h_prog_whilebody_cb p NONE s' = Ret (INL (p,s'))
  (* nice! this syntax is valid *)
  ∧ h_prog_whilebody_cb p res s' = Ret (INR (res,s'))
End

Definition h_prog_while_cb_def[simp]:
    h_prog_while_cb (p,s) NONE = Ret (INR (SOME Error,s))
  ∧ h_prog_while_cb (p,s) (SOME (ValWord w))
    = (if (w ≠ 0w)
       then Vis (INL (p,s))
                (λ(res,s'). h_prog_whilebody_cb p res s')
       else Ret (INR (NONE,s)))
  ∧ h_prog_while_cb (p,s) (SOME (ValLabel _)) = Ret (INR (SOME Error,s))
  ∧ h_prog_while_cb (p,s) (SOME (Struct _)) = Ret (INR (SOME Error,s))
End

Theorem h_prog_rule_while_alt:
  h_prog_rule_while g p s =
  iter (λ(p',s'). (h_prog_while_cb (p',s') (eval s' g))) (p,s)
Proof
  rw[h_prog_rule_while_def] >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE h_prog_while_cb_def] >>
  rw[DefnBase.one_line_ify NONE h_prog_whilebody_cb_def] >>
  rpt (PURE_TOP_CASE_TAC >> gvs[] >> rw[FUN_EQ_THM])
QED





(*/ testing recursive specifications
   TODO preludes and postludes, how to lift through to_ffi??
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

(*/ interp nonsense
   weird
 *)

Definition interp_cb_def[simp]:
  interp_cb rh (Ret r) = Ret (INR r) ∧
  interp_cb rh (Tau t) = Ret (INL t) ∧
  interp_cb rh (Vis e k) = bind (rh e) (λa. Ret (INL (k a)))
End

(* (E -> itree E' R) -> itree E R -> itree E' R *)
Definition itree_interp_def:
  itree_interp rh it = itree_iter (interp_cb rh) it
End

Theorem interp_cb_ret_inv:
  interp_cb rh t = Ret (INR r) ⇒ t = (Ret r)
Proof
  rw[DefnBase.one_line_ify NONE interp_cb_def] >>
  Cases_on ‘t’ >> fs[] >>
  Cases_on ‘rh a’ >> fs[]
QED

Theorem itree_interp_ret:
  itree_interp rh (Ret r) = Ret r
Proof
  rw[itree_interp_def] >>
  rw[Once itree_iter_thm]
QED

Theorem itree_interp_trigger:
  itree_interp rh (Vis e Ret) ≈ rh e
Proof
  rw[itree_interp_def] >>
  rw[Once itree_iter_thm] >>
  rw[itree_bind_assoc] >>
  rw[Once itree_iter_thm] >>
  irule itree_wbisim_coind >>
  qexists_tac ‘λa b. ∃t. a = bind t (λa. Tau (Ret a)) ∧ b = t’ >>
  rw[] >>
  Cases_on ‘a1’ >> rw[]
QED

Theorem itree_interp_bind:
  itree_interp rh (bind t k) = bind (itree_interp rh t) (λr. itree_interp rh (k r))
Proof
  rw[itree_interp_def] >>
  rw[Once itree_strong_bisimulation] >>
  qexists_tac ‘λa b. ∃ps. a = iter (interp_cb rh) (bind ps k) ∧
                          b = bind (iter (interp_cb rh) ps)
                                   (λx. iter (interp_cb rh) (k x))’ >>
  rw[] >-
   (metis_tac[])
   (cheat
   )
QED

(* they are only weakly bisimilar *)
Theorem itree_mrec_interp:
  iter (mrec_cb rh) t ≈
  itree_interp (λe. case e of
                      (INL a) => (itree_mrec rh a)
                    | (INR e) => Vis e Ret)
  t
Proof
  rw[Once itree_mrec_alt, itree_interp_def] >>
  rw[Once itree_iter_thm] >>
  CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV[itree_iter_thm] >>
  Cases_on ‘e’ >> rw[] >-
   (rw[itree_bind_assoc] >>
    rw[itree_mrec_bind] >>
    rw[GSYM itree_mrec_alt] >>
    cheat
   ) >-
   (rw[FUN_EQ_THM] >>
    rw[]
   )
QED
