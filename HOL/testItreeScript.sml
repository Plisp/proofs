open HolKernel boolLib bossLib BasicProvers;
open itreeTauTheory;
open panSemTheory; (* eval_def *)
open panItreeSemTheory;

(* open monadsyntax; *)
(* Overload monad_bind[local] = “itree_bind”; *)
(* Overload return[local] = “Ret”; *)

(* these are useful ONLY for bisimulation *)
val or1_tac = disj1_tac
val or2_tac = disj2_tac >> disj1_tac;
val or3_tac = disj2_tac >> disj2_tac;

(*/ basic examples of itree definition
   itree_unfold f is the final (coinductive) arrow to the capital algebra
   where f = structure map (into primed itree), seed = itree algebra instance
 *)

Theorem spin_unfold:
  spin = Tau spin
Proof
  rw[spin, Once itree_unfold]
QED

(* echo taken from paper, a bit different with HOL unfold vs deptypes *)

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

(*/ basic rephrasings
   not sure whether this should be kept around but lemmas use it atm
 *)

(* iiter (Ret INL) → Tau (itree_unfold (iiter_cb (mrec_cb h_prog))
                           (mrec_cb h_prog (⋆ (rh state_res) k))) to continue *)
(* mrec: Vis (INL (prog × newstate)) k → Ret (INL (h_prog prog ⋆ k)) *)
Definition mrec_cb_def[simp]:
  mrec_cb rh (Ret r) = Ret (INR r) ∧
  mrec_cb rh (Tau t) = Ret (INL t) ∧
  mrec_cb rh (Vis (INL state_res) k) = Ret (INL (⋆ (rh state_res) k)) ∧
  mrec_cb rh (Vis (INR ffi_res) k) = Vis ffi_res (λx. Ret (INL (k x)))
End

Theorem itree_mrec_alt:
  itree_mrec rh seed = itree_iter (mrec_cb rh) (rh seed)
Proof
  rw[itree_mrec_def] >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE mrec_cb_def]
QED

(* Dec cleanup *)

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

(*/ various abstract nonsense
   just to have a richer equational theory, unfold continuations suck to read
 *)

(* TODO itree_wbisim_tau is overloaded! merged. change later *)
Triviality itree_wbisim_add_tau:
  ∀ t. ≈ (Tau t) t
Proof
  qspecl_then [‘λa b. a = Tau b’] strip_assume_tac itree_wbisim_strong_coind >>
  strip_tac >>
  pop_assum irule >>
  rw[] >>
  Cases_on ‘t'’ >> rw[] >>
  disj2_tac >>
  rw[itree_wbisim_refl]
QED

(* TODO does this even hold*)
(* Theorem itree_wbisim_stronger_coind: *)
(*   !R. *)
(*     (!t t'. *)
(*        R t t' ==> *)
(*        (?t2 t3. t = Tau t2 /\ t' = Tau t3 /\ (R t2 t3 \/ itree_wbisim t2 t3)) \/ *)
(*        (?e k k'. *)
(*           strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\ *)
(*           !r. R (k r) (k' r) \/ itree_wbisim(k r) (k' r)) \/ *)
(*        (?r. strip_tau t (Ret r) /\ strip_tau t' (Ret r)) ∨ *)
(*        itree_wbisim t t') ==> *)
(*     !t t'. R t t' ==> itree_wbisim t t' *)
(* Proof *)
(*   rpt strip_tac \\ *)
(*   Q.SUBGOAL_THEN ‘R t t' \/ itree_wbisim t t'’ mp_tac THEN1 simp[] \\ *)
(*   pop_assum kall_tac \\ *)
(*   MAP_EVERY qid_spec_tac [‘t'’,‘t’] \\ *)
(*   ho_match_mp_tac itree_wbisim_coind \\ *)
(*   rw[] \\ *)
(*   res_tac \\ *)
(*   gvs[] \\ *)
(*   pop_assum (strip_assume_tac o ONCE_REWRITE_RULE[itree_wbisim_cases]) \\ *)
(*   metis_tac[] *)
(* QED *)

(* here's a nicer proof *)
Theorem itree_bind_resp_wbisim_ret_ret:
  ∀a b. (≈ a b) ∧ (∃ra rb. (a = Ret ra) ∧ (b = Ret rb))
        ⇒ ∀k1 k2. (∀r. ≈ (k1 r) (k2 r)) ⇒ (≈ (⋆ a k1) (⋆ b k2))
Proof
  rw[itree_bind_thm] >>
  rw[itree_bind_thm] >>
  ‘ra = rb’ by fs[Once itree_wbisim_cases] >>
  rw[]
QED

Theorem itree_bind_resp_wbisim:
  ∀a b. (≈ a b) ⇒ ∀k1 k2. (∀r. ≈ (k1 r) (k2 r)) ⇒ (≈ (⋆ a k1) (⋆ b k2))
Proof
  rpt strip_tac >>
  qspecl_then [‘λa b. ∃t1 t2. (≈ t1 t2) ∧ a = (⋆ t1 k1) ∧ b = (⋆ t2 k2)’]
              strip_assume_tac itree_wbisim_strong_coind >>
  pop_assum irule >>
  rw[] >-
   (last_x_assum kall_tac >>
    Cases_on ‘t1’ >>
    Cases_on ‘t2’ >-
     cheat >- (* Ret Ret TODO how to strengthen the IH? *)
     (* Ret Tau TODO extract and flip this by symmetry *)
     cheat >-
     (* Ret Vis is impossible *)
     fs[Once itree_wbisim_cases] >-
     (* Tau Ret *)
     cheat >-
     (* Tau Tau *)
     (or1_tac >>
      rw[itree_bind_thm] >>
      ‘≈ u u'’ by metis_tac[itree_wbisim_tau, itree_wbisim_sym] >>
      metis_tac[itree_bind_resp_wbisim_ret_ret]) >-
     (* Tau Vis *)
     cheat >-
     (* Vis Ret impossible. duplicated but trivial *)
     fs[Once itree_wbisim_cases] >-
     (* Vis Tau *)
     cheat >-
     (* Vis Vis annoying to rewrite, requires wbisim *)
     (or2_tac >>
      rw[itree_bind_thm] >-
       fs[Once itree_wbisim_cases] >-
       (qspecl_then [‘(Vis a g)’, ‘(Vis a' g')’]
                    strip_assume_tac itree_wbisim_cases >>
        fs[] >>
        metis_tac[itree_bind_resp_wbisim_ret_ret])))
  >- metis_tac[]
QED

(* Theorem itree_iter_resp_wbisim: *)
(*   ∀a b rh1 rh2 seed1 seed2. *)
(*   ≈ seed1 seed2 *)
(*   ∧ ∀s. (≈ (rh1 s) (rh2 s)) *)
(*   ⇒ (≈ (itree_iter rh1 seed1) (itree_iter rh2 seed2)) *)
(* Proof *)
(*   (* TODO! *) *)
(* QED *)

(* f, f' type vars instantiated differently smh *)
Theorem mrec_bind_lemma:
  ∀f f'.
  (∀a. ∃r. (f a) = (Ret r) ∧ (f' a) = (Ret r)) ⇒
  ∀t. (itree_iter (mrec_cb h_prog) (⋆ t f)) =
      (⋆ (itree_iter (mrec_cb h_prog) t) f')
Proof
  rpt strip_tac >>
  qspecl_then [‘itree_iter (mrec_cb h_prog) (⋆ t f)’,
               ‘⋆ (itree_iter (mrec_cb h_prog) t) f'’]
              strip_assume_tac itree_bisimulation >>
  fs[EQ_IMP_THM] >>
  qpat_x_assum ‘_ ⇒ ∃R. _’ kall_tac >>
  pop_assum irule >>
  qexists_tac
  ‘λa b. ∃t name s.
    a = (itree_iter (mrec_cb h_prog) (⋆ t f)) ∧
    b = (⋆ (itree_iter (mrec_cb h_prog) t) f')’ >>
  rw[] >-
   metis_tac[] >- (* base case *)
   (* ret *)
   (Cases_on ‘t'’ >-
     (fs[Once itree_iter_thm, itree_bind_thm] >>
      last_assum (qspec_then ‘x'’ strip_assume_tac) >>
      fs[itree_bind_thm]) >-
     (fs[Once itree_iter_thm, itree_bind_thm]) >-
     (Cases_on ‘a’ >-
       fs[Once itree_iter_thm, itree_bind_thm] >-
       fs[Once itree_iter_thm, itree_bind_thm])) >-
   (* tau *)
   (Cases_on ‘t'’ >-
     (fs[Once itree_iter_thm, itree_bind_thm] >>
      last_assum (qspec_then ‘x’ strip_assume_tac) >>
      fs[itree_bind_thm]) >-
     (fs[Once itree_iter_thm, itree_bind_thm] >>
      metis_tac[]) >-
     (Cases_on ‘a’ >-
       (fs[Once itree_iter_thm, itree_bind_thm] >>
        metis_tac[GSYM itree_bind_assoc]) >-
       fs[Once itree_iter_thm, itree_bind_thm])) >-
   (* vis *)
   (Cases_on ‘t'’ >-
     (fs[Once itree_iter_thm, itree_bind_thm] >>
      last_assum (qspec_then ‘x’ strip_assume_tac) >>
      fs[itree_bind_thm]) >-
     fs[Once itree_iter_thm, itree_bind_thm] >-
     (Cases_on ‘a'’ >-
       fs[Once itree_iter_thm, itree_bind_thm] >-
       (fs[Once itree_iter_thm, itree_bind_thm] >>
        strip_tac >>
        (* TODO stuck on extra Tau from iter on (Ret INL) from (Vis INR) *)
       )))
QED

(* relies on mrec_cb h_prog rev -> only Ret INR, so can't prolong iteration *)
(* also applies to while and cond! *)
Theorem dec_lemma:
  ∀ t name s.
    ≈ (itree_iter (mrec_cb h_prog) (⋆ t (revert_binding name s)))
      (⋆ (itree_iter (mrec_cb h_prog) t) (revert_binding name s))
Proof
  qspecl_then
  [‘λa b. ∃t name s.
     a = (itree_iter (mrec_cb h_prog) (⋆ t (revert_binding name s))) ∧
     b = (⋆ (itree_iter (mrec_cb h_prog) t) (revert_binding name s))’]
  strip_assume_tac itree_wbisim_strong_coind >>
  rpt strip_tac >>
  pop_assum irule >>
  rw[] >-
   (Cases_on ‘t''’ >-
     (or3_tac >> (* Ret produces Ret, doesn't affect iter. easy! *)
      Cases_on ‘x’ >>
      rw[revert_binding_def] >>
      rw[Once itree_iter_thm, itree_bind_thm] >>
      rw[Once itree_iter_thm, itree_bind_thm]) >-
     (* Tau case is clear *)
     (or1_tac >>
      rw[Once itree_iter_thm, itree_bind_thm] >>
      rw[Once itree_iter_thm, itree_bind_thm] >>
      metis_tac[]) >-
     (* Vis case is a bit tricky, depends on whether the event is silent *)
     (Cases_on ‘a’ >-
       (or1_tac >>
        rw[Once itree_iter_thm, itree_bind_thm] >>
        rw[Once itree_iter_thm, itree_bind_thm] >>
        metis_tac[GSYM itree_bind_assoc]) >-
       (or2_tac >>
        rw[Once itree_iter_thm, itree_bind_thm] >>
        rw[Once itree_iter_thm, itree_bind_thm] >>
        or1_tac >>
        qexistsl_tac [‘Tau (g r)’, ‘name’, ‘s’] >>
        CONJ_TAC >-
         (CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV[itree_bind_thm] >>
          CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV[itree_iter_thm] >>
          rw[itree_bind_thm]) >-
         (CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV[itree_iter_thm] >>
          rw[itree_bind_thm])))) >-
   metis_tac[]
QED

Theorem dec_thm:
  (eval s e = SOME k) ⇒
  ≈ (itree_mrec h_prog (Dec name e p,s))
    (⋆
     (itree_mrec h_prog (p,s with locals := s.locals |+ (name,k)))
     (revert_binding name s))
Proof
  rw[itree_mrec_alt] >>
  rw[h_prog_def, h_prog_rule_dec_def] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  rw[GSYM revert_binding_def] >>
  metis_tac[dec_lemma, itree_wbisim_add_tau, itree_wbisim_trans]
QED

(*/ massaging into ffi itree
   this doesn't have a nice theory but simps should do most of the work
 *)

Definition massage_cb_def[simp]:
    massage_cb (INL (Ret (res, s))) = Ret' res
  ∧ massage_cb (INR (Ret (res',s'))) = Ret' res'
  ∧ massage_cb (INL (Tau t)) = Tau' (INL t)
  ∧ massage_cb (INR (Tau t')) = Tau' (INR t')
  ∧ massage_cb (INL (Vis (e,k) g)) = Vis' e (λr. INR (k r))
  ∧ massage_cb (INR (Vis e' g')) = Vis' e' (INR ∘ g')
End

(* massage Ret type from (η x state) -> η *)
(* convert Vis (sem_vis_event x (FFI_result -> itree)) ((prog x state) -> %itree)
-> Vis sem_vis_event (FFI_result -> itree) *)
Definition massage_def:
  massage x = itree_unfold massage_cb (INL x)
End

Theorem massage_thm:
    massage (Ret (res, s)) = Ret res
  ∧ massage (Tau t) = Tau (massage t)
Proof
  rw[massage_def] >-
   rw[Once itree_unfold] >-
   (rw[Once itree_unfold] >> rw[GSYM massage_def])
QED

Theorem itree_evaluate_alt:
  itree_evaluate p s = massage (itree_mrec h_prog (p,s))
Proof
  rw[itree_evaluate_def, massage_def] >>
  AP_THM_TAC >> (* same fn => same on same arg, backwards *)
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE massage_cb_def]
QED

(*/ pancake programs
   & parsing utilities
 *)

open stringLib helperLib;
open finite_mapTheory; (* flookup_thm *)

open asmTheory; (* word_cmp_def *)
open miscTheory; (* read_bytearray *)
open panLangTheory; (* size_of_shape_def *)
open panPtreeConversionTheory; (* parse_funs_to_ast *)
open wordLangTheory; (* word_op_def *)
open wordsTheory; (* n2w_def *)

local
  val f =
    List.mapPartial
       (fn s => case remove_whitespace s of "" => NONE | x => SOME x) o
    String.tokens (fn c => c = #"\n")
in
  fun quote_to_strings q =
    f (Portable.quote_to_string (fn _ => raise General.Bind) q)
  end

fun parse_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “parse_funs_to_ast ^code”
end

(* ffi test *)

val ffi_ast = rhs $ concl $ parse_pancake ‘
fun fn() {
  #num_clients(0, 0, 0, 0);
  #num_clients(0, 0, 0, 0);
}’;

Definition ffi_sem_def:
  ffi_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD $ THE ^ffi_ast) s
End

Theorem ffi_sem_thm:
  ffi_sem s = ARB
Proof
  rw[ffi_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  (* Seq *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_seq_def] >>
  rw[Once itree_iter_thm, Once itree_bind_thm] >>
  (* extcall *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[eval_def, FLOOKUP_UPDATE] >>
  rw[read_bytearray_def] >>
  rw[Once itree_bind_thm] >>
  rw[Once itree_iter_thm] >>
  rw[Once itree_bind_thm] >>
  (* inner thing *)
  rw[Once itree_bind_thm] >>
  rw[Once itree_bind_thm] >>
  (* TODO massage bug! (not yet fixed, update when done) *)
  rw[massage_def] >>
  rw[Once itree_unfold, massage_thm] >>
  rw[Once itree_unfold]
QED

(* manual loop unrolling isn't too bad with equational rewrites *)

val loop_ast = rhs $ concl $ parse_pancake ‘
fun fn() {
  var x = 0;
  while (x < 1) {
    x = x + 1;
  }
}’;

Definition loop_sem_def:
  loop_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD $ THE ^loop_ast) s
End

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
  itree_iter (λ(p', s'). (h_prog_while_cb (p',s') (eval s' g))) (p,s)
Proof
  (* TODO this should be updated in the semantics *)
  cheat
  (* rw[h_prog_rule_while_def] >> *)
  (* AP_THM_TAC >> *)
  (* AP_TERM_TAC >> *)
  (* rw[FUN_EQ_THM] >> *)
  (* rw[DefnBase.one_line_ify NONE h_prog_while_cb_def] >> *)
  (* rw[DefnBase.one_line_ify NONE h_prog_whilebody_cb_def] >> *)
  (* rpt (PURE_TOP_CASE_TAC >> gvs[] >> rw[FUN_EQ_THM]) *)
QED

Theorem cheat1:
  0w < 1w (* supposed to be :4 word but w/e *)
Proof
  cheat
QED

Theorem loop_thm:
  loop_sem s = Tau (Tau (Tau (Ret NONE)))
Proof
  rw[loop_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_dec_alt] >>
  rw[eval_def] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  (* while *)
  rw[Once h_prog_def, h_prog_rule_while_alt] >>
  rw[Once itree_iter_thm] >>
  rw[Once itree_iter_thm] >>
  rw[eval_def, FLOOKUP_UPDATE, word_cmp_def, cheat1] >>
  rw[itree_bind_thm] >>
  (* assignment *)
  rw[Once h_prog_def, h_prog_rule_assign_def] >>
  rw[eval_def, FLOOKUP_UPDATE, cheat1,
     word_op_def, is_valid_value_def, shape_of_def] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  (* second while *)
  rw[Once itree_iter_thm] >>
  rw[Once itree_iter_thm] >>
  rw[eval_def, FLOOKUP_UPDATE, word_cmp_def] >>
  rw[revert_binding_def] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  (* massage *)
  rw[massage_thm]
QED
