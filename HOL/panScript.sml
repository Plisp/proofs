(*
 * actual pancake programs. simps used here
 *)

open panPtreeConversionTheory; (* parse_funs_to_ast *)
open panSemTheory; (* eval_def *)

local
  val f =
    List.mapPartial
       (fn s => case helperLib.remove_whitespace s of "" => NONE | x => SOME x) o
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

(* TODO needs to be in panSemTheory *)
Theorem pan_eval_simps[simp]:
    eval s (Const w) = SOME (ValWord w)
  ∧ eval s (Var v) = FLOOKUP s.locals v
  ∧ eval s BaseAddr = SOME (ValWord s.base_addr)
  ∧ eval s (Label fname) = OPTION_IGNORE_BIND (FLOOKUP s.code fname)
                                              (SOME (ValLabel fname))
Proof
  rw[eval_def] >>
  Cases_on ‘FLOOKUP s.code fname’ >> rw[]
QED

(* word related nonsense *)
Theorem load_write_bytearray_thm:
  (∀(b : word8). byte_align b = b) ⇒
  (∀(w : word8). w ∈ s.memaddrs) ⇒
  (∀w. ∃(k : word8). oldmem w = Word k) ⇒
  mem_load_byte (write_bytearray 0w [v] oldmem s.memaddrs s.be)
                s.memaddrs s.be 0w
  = SOME v
Proof
  rw[mem_load_byte_def] >>
  rw[write_bytearray_def] >>
  rw[mem_store_byte_def] >>
  first_assum $ qspec_then ‘0w’ strip_assume_tac >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  rw[byteTheory.get_byte_set_byte]
QED

Theorem write_bytearray_preserve_words:
  (∀w. ∃(k : word8). s.memory w = Word k) ⇒
  ∀w. ∃(k : word8). (write_bytearray loc l s.memory s.memaddrs s.be) w = Word k
Proof
  strip_tac >>
  qid_spec_tac ‘loc’ >>
  Induct_on ‘l’ >>
  rw[write_bytearray_def] >>
  fs[mem_store_byte_def] >>
  Cases_on ‘write_bytearray (loc+1w) l s.memory s.memaddrs s.be (byte_align loc)’ >>
  rw[] >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on ‘byte_align loc = w’ >> rw[]
QED

(*/
  ffi skip test
 *)

val ffi_ast = rhs $ concl $ parse_pancake ‘
fun fn() {
  #f1(0, 0, 0, 0);
  #f2(0, 0, @base, 1);
  if (ldb @base) == 0 {
    #f3(0, 0, 0, 0);
  } else {
    #f4(0, 0, 0, 0);
  }
}’;
(* memaddrs *)

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

(* RTC of above AF CTL *)
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

Theorem write_bytearray_id:
  (∀(b : word8). byte_align b = b) ⇒
  (∀(w : word8). w ∈ s.memaddrs) ⇒
  (∀w. s.memory w = Word (0w : 8 word)) ⇒
  mem_load_byte (write_bytearray 0w [v]
                                 (write_bytearray loc l s.memory s.memaddrs s.be)
                                 s.memaddrs s.be)
                s.memaddrs s.be 0w
  = SOME v
Proof
  metis_tac[write_bytearray_preserve_words, load_write_bytearray_thm]
QED

(* TODO simp for future_cases *)
Theorem ffi_sem_thm:
  (s.base_addr = 0w) ⇒
  (∀(b : word8). byte_align b = b) ⇒
  (∀w. s.memory w = Word (0w : 8 word)) ⇒
  (∀(w : word8). w ∈ s.memaddrs) ⇒
  r1 = [0w : 8 word] ⇒
  future (λt. (∃k k'. k (FFI_return ARB r1) ≈ (Vis (FFI_call "f3" [] []) k') ∧
                      (t = Vis (FFI_call "f2" [] []) k)) ∨
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
  rw[miscTheory.read_bytearray_def] >>
  (* massaging *)
  rw[Once future_cases] >> disj2_tac >>
  rw[Once future_cases] >> disj2_tac >>
  strip_tac >>
  (* forall a?, doesn't matter here! *)
  rw[Once future_cases] >> disj2_tac >>
  reverse (Cases_on ‘a’) >-
   (qunabbrev_tac ‘P’ >>
    rw[Once future_cases] >> disj1_tac) >>
  rw[Once future_cases] >> disj2_tac >>
  (* second seq *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_seq_def] >>
  rw[Once itree_iter_thm, Once itree_bind_thm] >>
  (* extcall *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[miscTheory.read_bytearray_def] >>
  rw[Once future_cases] >> disj2_tac >>
  rw[Once future_cases] >> disj1_tac >>
  qunabbrev_tac ‘P’ >> rw[] >>
  (* cond *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
  rw[eval_def, asmTheory.word_cmp_def] >>
  rw[write_bytearray_id] >>
  (* third call happens *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[miscTheory.read_bytearray_def] >>
  metis_tac[itree_wbisim_refl]
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
