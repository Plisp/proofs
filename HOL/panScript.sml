(*
 * actual pancake programs. simps used here
 *)

open panItreeSemTheory;
open panSemTheory; (* eval_def *)

(*/ equational theorems for mrec
   mrec expresses a recursive computation by iterating Vis INL
   TODO should this be in the itreeTauTheory? Yes
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
   equational pancake itrees
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

(*/ massaging into ffi itree
   TODO merge
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

Theorem itree_evaluate_alt:
  itree_evaluate p s = to_ffi (itree_mrec h_prog (p,s))
Proof
  rw[itree_evaluate_def, to_ffi_def] >>
  AP_THM_TAC >> (* same fn => same on same arg, backwards *)
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE massage_cb_def, combinTheory.o_DEF]
QED

open finite_mapTheory; (* FLOOKUP_UPDATE *)
open helperLib; (* remove_whitespace *)
(* open wordsTheory; (* n2w_def *) *)

open asmTheory; (* word_cmp_def *)
open miscTheory; (* read_bytearray *)
open panLangTheory; (* size_of_shape_def *)
open panPtreeConversionTheory; (* parse_funs_to_ast *)
open wordLangTheory; (* word_op_def *)

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

(*/
  ffi skip test
 *)

val ffi_ast = rhs $ concl $ parse_pancake ‘
fun fn() {
  #f1(0, 0, 0, 0);
  #f2(0, 0, 0, 0);
  #f3(0, 0, 0, 0);
  #f4(0, 0, 0, 0);
}’;

Definition ffi_sem_def:
  ffi_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD $ THE ^ffi_ast) s
End

(* Inductive walk: *)
(* [~Tau:] (∀t. (walk t responses result ⇒ walk (Tau t) responses result)) ∧ *)
(* [~Vis:] (∀k e r. walk (k r) responses result *)
(*            ⇒ walk (Vis e k) (r::responses) ((e,r)::result)) ∧ *)
(* [~Ret:] (∀r. walk (Ret r) [] []) *)
(* End *)

Inductive next:
  (P (Ret r) ⇒ next P (Ret r)) ∧
  (P (Tau t) ⇒ next P t) ∧
  ((∀a. P (k a)) ⇒ next P (Vis e k))
End

(* RTC of above *)
Inductive future:
  (P t ⇒ future P t) ∧
  (future P t ⇒ future P (Tau t)) ∧
  ((∀a. future P (k a)) ⇒ future P (Vis e k))
End

Definition the_ffi_def:
  the_ffi t res f =
  (∃q. t = (case res of
              FFI_return new_ffi new_bytes => f new_ffi new_bytes
            | FFI_final outcome => q outcome))
End

Theorem pull_ffi_case:
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

Theorem itree_wbisim_drop_tau:
  ∀t. t ≈ t' ⇒ Tau t ≈ t
Proof
  metis_tac[itree_wbisim_tau_eq, itree_wbisim_trans]
QED

Theorem ffi_sem_thm:
  future (λt. (∃k k'. (t = Vis (FFI_call "f3" [] []) k) ∧
                      k (FFI_return ARB ARB) ≈ (Vis (FFI_call "f4" [] []) k')) ∨
              (∃outcome. t = Ret (SOME (FinalFFI outcome))))
  (ffi_sem s)
Proof
  qmatch_goalsub_abbrev_tac ‘future P (ffi_sem _)’ >>
  rw[ffi_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  (* Seq rw[seq_thm] *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_seq_def] >>
  rw[Once itree_iter_thm, Once itree_bind_thm] >>
  (* extcall *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[eval_def, FLOOKUP_UPDATE] >>
  rw[read_bytearray_def] >>
  (* massaging *)
  rw[Once future_cases] >> disj2_tac >>
  rw[Once future_cases] >> disj2_tac >>
  rw[Once future_cases] >> disj2_tac >>
  rw[pull_ffi_case] >>
  reverse (Cases_on ‘a’) >-
   (fs[Once future_cases] >>
    metis_tac[]) >>
  rw[Once future_cases] >> disj2_tac >>
  (* Seq *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_seq_def] >>
  rw[Once itree_iter_thm, Once itree_bind_thm] >>
  (* extcall *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[eval_def, FLOOKUP_UPDATE] >>
  rw[read_bytearray_def] >>
  (* *)
  rw[Once future_cases] >> disj2_tac >>
  rw[Once future_cases] >> disj2_tac >>
  rw[Once future_cases] >> disj2_tac >>
  rw[pull_ffi_case] >>
  reverse (Cases_on ‘a’) >-
   (fs[Once future_cases] >>
    metis_tac[]) >>
  rw[Once future_cases] >> disj2_tac >>
  (* extcall *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[eval_def, FLOOKUP_UPDATE] >>
  rw[read_bytearray_def] >>
  (* seq *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_seq_def] >>
  rw[Once itree_iter_thm, Once itree_bind_thm] >>
  (* extcall *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[eval_def, FLOOKUP_UPDATE] >>
  rw[read_bytearray_def] >>
  rw[Once future_cases] >> disj2_tac >>
  rw[Once future_cases] >> disj1_tac >>
  qunabbrev_tac ‘P’ >>
  rw[] >>
  (* extcall *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[eval_def, FLOOKUP_UPDATE] >>
  rw[read_bytearray_def] >>
  metis_tac[itree_wbisim_drop_tau, itree_wbisim_trans, itree_wbisim_refl]
QED

(*/ loops work!
   manual loop unrolling isn't too bad with equational rewrites
 *)

(* val loop_ast = rhs $ concl $ parse_pancake ‘ *)
(* fun fn() { *)
(*   var x = 1; *)
(*   x = 0; *)
(*   while (x < 1) { *)
(*     x = x + 1; *)
(*   } *)
(* }’; *)

(* Definition loop_sem_def: *)
(*   loop_sem (s:('a,'ffi) panSem$state) = *)
(*   itree_evaluate (SND $ SND $ HD $ THE ^loop_ast) s *)
(* End *)

(* Definition h_prog_whilebody_cb_def[simp]: *)
(*     h_prog_whilebody_cb p (SOME Break) s' = Ret (INR (NONE,s')) *)
(*   ∧ h_prog_whilebody_cb p (SOME Continue) s' = Ret (INL (p,s')) *)
(*   ∧ h_prog_whilebody_cb p NONE s' = Ret (INL (p,s')) *)
(*   (* nice! this syntax is valid *) *)
(*   ∧ h_prog_whilebody_cb p res s' = Ret (INR (res,s')) *)
(* End *)

(* Definition h_prog_while_cb_def[simp]: *)
(*     h_prog_while_cb (p,s) NONE = Ret (INR (SOME Error,s)) *)
(*   ∧ h_prog_while_cb (p,s) (SOME (ValWord w)) *)
(*     = (if (w ≠ 0w) *)
(*        then Vis (INL (p,s)) *)
(*                 (λ(res,s'). h_prog_whilebody_cb p res s') *)
(*        else Ret (INR (NONE,s))) *)
(*   ∧ h_prog_while_cb (p,s) (SOME (ValLabel _)) = Ret (INR (SOME Error,s)) *)
(*   ∧ h_prog_while_cb (p,s) (SOME (Struct _)) = Ret (INR (SOME Error,s)) *)
(* End *)

(* (* PR submitted *) *)
(* Theorem h_prog_rule_while_alt: *)
(*   h_prog_rule_while g p s = *)
(*   iter (λ(p',s'). (h_prog_while_cb (p',s') (eval s' g))) (p,s) *)
(* Proof *)
(*   rw[h_prog_rule_while_def] >> *)
(*   AP_THM_TAC >> *)
(*   AP_TERM_TAC >> *)
(*   rw[FUN_EQ_THM] >> *)
(*   rw[DefnBase.one_line_ify NONE h_prog_while_cb_def] >> *)
(*   rw[DefnBase.one_line_ify NONE h_prog_whilebody_cb_def] >> *)
(*   rpt (PURE_TOP_CASE_TAC >> gvs[] >> rw[FUN_EQ_THM]) *)
(* QED *)

(* Theorem cheat1: *)
(*   0w < 1w (* supposed to be :4 word but weever *) *)
(* Proof *)
(*   cheat *)
(* QED *)

(* Theorem loop_thm: *)
(*   loop_sem s =  Tau (Tau (Tau (Tau (Tau (Ret NONE))))) *)
(* Proof *)
(*   rw[loop_sem_def, itree_semantics_def, itree_evaluate_alt] >> *)
(*   rw[itree_mrec_alt, h_prog_def, h_prog_rule_dec_alt] >> *)
(*   rw[eval_def] >> *)
(*   rw[Once itree_iter_thm, itree_bind_thm] >> *)
(*   (* seq *) *)
(*   rw[h_prog_def, h_prog_rule_seq_def] >> *)
(*   rw[itree_bind_thm] >> *)
(*   rw[Once itree_iter_thm] >> *)
(*   rw[Once itree_bind_thm] >> *)
(*   (* assign *) *)
(*   rw[Once h_prog_def, h_prog_rule_assign_def] >> *)
(*   rw[FLOOKUP_UPDATE, word_op_def, is_valid_value_def, shape_of_def, *)
(*      Once eval_def, cheat1] >> *)
(*   rw[itree_bind_thm] >> *)
(*   rw[Once itree_iter_thm, Once itree_bind_thm] >> *)
(*   (* while *) *)
(*   rw[Once h_prog_def, h_prog_rule_while_alt] >> *)
(*   rw[Once itree_iter_thm] >> rw[Once itree_iter_thm] >> *)
(*   rw[Once eval_def] >> rw[Once eval_def] >> *)
(*   rw[FLOOKUP_UPDATE] >> *)
(*   rw[Once eval_def, word_cmp_def, cheat1] >> *)
(*   rw[itree_bind_thm] >> *)
(*   (* assignment *) *)
(*   rw[Once h_prog_def, h_prog_rule_assign_def] >> *)
(*   rw[Once eval_def] >> rw[Once eval_def] >> *)
(*   rw[FLOOKUP_UPDATE, word_op_def, is_valid_value_def, shape_of_def, *)
(*      Once eval_def, cheat1] >> *)
(*   rw[Once itree_iter_thm, itree_bind_thm] >> *)
(*   (* second while *) *)
(*   (* rw[GSYM h_prog_rule_while_alt, GSYM h_prog_def] *) *)
(*   rw[Once itree_iter_thm] >> rw[Once itree_iter_thm] >> *)
(*   rw[eval_def, FLOOKUP_UPDATE, word_cmp_def] >> *)
(*   rw[revert_binding_def] >> *)
(*   rw[Once itree_iter_thm, itree_bind_thm] >> *)
(*   (* massage *) *)
(*   rw[massage_thm] *)
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
