(*
 * actual pancake programs. simps used here
 *)

open panItreeSemTheory;
open panSemTheory; (* eval_def *)

(*/ equational
   not sure whether this should be kept around but lemmas use it atm
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
  rw[DefnBase.one_line_ify NONE mrec_cb_def]
QED

Theorem iter_mrec_cb_thm[simp]:
  iter (mrec_cb h_prog) (Ret x) = Ret x ∧
  iter (mrec_cb h_prog) (Tau t) = Tau (iter (mrec_cb h_prog) t) ∧
  iter (mrec_cb h_prog) (Vis (INL s) g)
    = Tau (iter (mrec_cb h_prog) (bind (h_prog s) g)) ∧
  iter (mrec_cb h_prog) (Vis (INR e) k)
    = Vis e (λx. Tau (iter (mrec_cb h_prog) (k x)))
Proof
  rw[Once itree_iter_thm] >> rw[Once itree_iter_thm]
QED

(*/ Seq thm
   this is how we split up a program
 *)

(* inversion lemmas *)
Theorem itree_bind_ret_inv:
  bind t k = Ret r ⇒ ∃r'. t = Ret r' ∧ Ret r = (k r')
Proof
  Cases_on ‘t’ >> fs[]
QED

Theorem mrec_cb_ret_inv:
  mrec_cb rh t = Ret (INR r) ⇒ t = (Ret r)
Proof
  rw[DefnBase.one_line_ify NONE mrec_cb_def] >>
  Cases_on ‘t’ >> fs[] >-
   (Cases_on ‘a’ >> fs[])
QED

(* h_prog iterates sequentially on its seed *)
Theorem mrec_bind_thm:
  ∀t k. iter (mrec_cb h_prog) (bind t k) =
        bind (iter (mrec_cb h_prog) t) (λx. iter (mrec_cb h_prog) (k x))
Proof
  rw[Once itree_strong_bisimulation] >>
  qexists_tac ‘λa b. ∃ps. a = iter (mrec_cb h_prog) (bind ps k) ∧
                          b = bind (iter (mrec_cb h_prog) ps)
                                (λx. iter (mrec_cb h_prog) (k x))’ >>
  rw[] >-
   (metis_tac[]) >-
   (‘bind (mrec_cb h_prog (bind ps k))
       (λx. case x of INL a => Tau (iter (mrec_cb h_prog) a) | INR b => Ret b)
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

Theorem mrec_seq_thm:
  iter (mrec_cb h_prog)
     (bind t
        (λ(res,s'). if res = NONE then Vis (INL (p2,s')) Ret else Ret (res,s')))
  = bind (iter (mrec_cb h_prog) t)
      (λ(res,s').
         if res = NONE then Tau (iter (mrec_cb h_prog) (h_prog (p2,s')))
         else Ret (res,s'))
Proof
  rw[mrec_bind_thm] >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  Cases_on ‘x’ >> rw[]
QED

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
  rw[mrec_seq_thm]
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

(* f, f' type vars instantiated differently smh *)
(* relies on mrec_cb h_prog rev -> only Ret INR, so can't prolong iteration *)
Theorem mrec_bind_ret:
  ∀f f'.
    (∀a. ∃r. (f a) = (Ret r) ∧ (f' a) = (Ret r)) ⇒
    ∀t. iter (mrec_cb h_prog) (bind t f) = (bind (iter (mrec_cb h_prog) t) f')
Proof
  rpt strip_tac >>
  rw[mrec_bind_thm] >>
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
  irule mrec_bind_ret >>
  rw[revert_binding_def] >>
  Cases_on ‘a’ >> rw[]
QED

(*/ massaging into ffi itree
   TODO change when fixed
 *)

Definition massage_cb_def[simp]:
    massage_cb (INL stree) = massage stree ∧
    massage_cb (INR (Ret res_state,st)) = massage (st res_state) ∧
    massage_cb (INR (Tau kt,st)) = Tau' (INR (kt,st)) ∧
    massage_cb (INR (Vis svis_ev kt',st))
    = Vis' svis_ev (λffi_res. INR (kt' ffi_res,st))
End

(* massage Ret type from (η x state) -> η *)
(* convert Vis (sem_vis_event x (FFI_result -> itree)) ((prog x state) -> %itree)
-> Vis sem_vis_event (FFI_result -> itree) *)
Definition to_ffi_def:
  to_ffi x = itree_unfold massage_cb (INL x)
End

Theorem itree_evaluate_alt:
  itree_evaluate p s = to_ffi (itree_mrec h_prog (p,s))
Proof
  rw[itree_evaluate_def, to_ffi_def] >>
  AP_THM_TAC >> (* same fn => same on same arg, backwards *)
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  rw[DefnBase.one_line_ify NONE massage_cb_def]
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

(*/ loops work!
   manual loop unrolling isn't too bad with equational rewrites
 *)

val loop_ast = rhs $ concl $ parse_pancake ‘
fun fn() {
  var x = 1;
  x = 0;
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

(* PR submitted *)
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

Theorem cheat1:
  0w < 1w (* supposed to be :4 word but weever *)
Proof
  cheat
QED

Theorem mrec_thm:
  iter (mrec_cb h_prog) (bind t k)
  ≈ bind (iter (mrec_cb h_prog) t) (λr. iter (mrec_cb h_prog) (k r))
Proof
  CONV_TAC $ RHS_CONV $ REWRITE_CONV[Once itree_iter_thm, mrec_cb_def] >>
  CONV_TAC $ RHS_CONV $ REWRITE_CONV[Once itree_bind_thm] >>
  rw[itree_bind_thm]
QED

Theorem loop_thm:
  loop_sem s =  Tau (Tau (Tau (Tau (Tau (Ret NONE)))))
Proof
  rw[loop_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_dec_alt] >>
  rw[eval_def] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  (* seq *)
  rw[h_prog_def, h_prog_rule_seq_def] >>
  rw[itree_bind_thm] >>
  rw[Once itree_iter_thm] >>
  rw[Once itree_bind_thm] >>
  (* assign *)
  rw[Once h_prog_def, h_prog_rule_assign_def] >>
  rw[FLOOKUP_UPDATE, word_op_def, is_valid_value_def, shape_of_def,
     Once eval_def, cheat1] >>
  rw[itree_bind_thm] >>
  rw[Once itree_iter_thm, Once itree_bind_thm] >>
  (* while *)
  rw[Once h_prog_def, h_prog_rule_while_alt] >>
  rw[Once itree_iter_thm] >> rw[Once itree_iter_thm] >>
  rw[Once eval_def] >> rw[Once eval_def] >>
  rw[FLOOKUP_UPDATE] >>
  rw[Once eval_def, word_cmp_def, cheat1] >>
  rw[itree_bind_thm] >>
  (* assignment *)
  rw[Once h_prog_def, h_prog_rule_assign_def] >>
  rw[Once eval_def] >> rw[Once eval_def] >>
  rw[FLOOKUP_UPDATE, word_op_def, is_valid_value_def, shape_of_def,
     Once eval_def, cheat1] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  (* second while *)
  (* rw[GSYM h_prog_rule_while_alt, GSYM h_prog_def] *)
  rw[Once itree_iter_thm] >> rw[Once itree_iter_thm] >>
  rw[eval_def, FLOOKUP_UPDATE, word_cmp_def] >>
  rw[revert_binding_def] >>
  rw[Once itree_iter_thm, itree_bind_thm] >>
  (* massage *)
  rw[massage_thm]
QED

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
  (* next, stuck *)
  rw[Once itree_iter_thm] >>
  (* massaging *)
  rw[to_ffi_def] >>
  rw[Once itree_unfold] >>
  rw[massage_def] >>
  rw[Once itree_unfold] >>
  rw[massage_def] >>
  rw[combinTheory.o_DEF] >>
QED
