(*
 * actual pancake programs. simps used here
 *)

open panPtreeConversionTheory; (* parse_funs_to_ast *)
open panSemTheory; (* eval_def *)
open arithmeticTheory

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
    rhs $ concl $ SRULE[] $ EVAL “THE (parse_funs_to_ast ^code)”
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

(* word nonsense *)
Theorem load_write_bytearray_thm:
  (∀(b : word8). byte_align b = b) ⇒
  (∀(w : word8). w ∈ s.memaddrs) ⇒
  (∀w. ∃(k : word8). oldmem w = Word k) ⇒
  mem_load_byte (write_bytearray addr [v] oldmem s.memaddrs s.be)
                s.memaddrs s.be addr
  = SOME v
Proof
  rw[mem_load_byte_def] >>
  rw[write_bytearray_def] >>
  rw[mem_store_byte_def] >>
  first_assum $ qspec_then ‘addr’ strip_assume_tac >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  rw[byteTheory.get_byte_set_byte]
QED

(* Theorem write_bytearray_preserve_words: *)
(*   (∀w. ∃(k : word8). loc ≤ w ∧ w ≤ (loc + LENGTH l) ⇒ s.memory w = Word k) ⇒ *)
(*   ∀w. ∃(k : word8). (write_bytearray loc l s.memory s.memaddrs s.be) w = Word k *)
(* Proof *)
(*   strip_tac >> *)
(*   qid_spec_tac ‘loc’ >> *)
(*   Induct_on ‘l’ >> *)
(*   rw[write_bytearray_def] >> *)
(*   fs[mem_store_byte_def] >> *)
(*   Cases_on ‘write_bytearray (loc+1w) l s.memory s.memaddrs s.be (byte_align loc)’ >> *)
(*   rw[] >> *)
(*   rw[combinTheory.APPLY_UPDATE_THM] >> *)
(*   Cases_on ‘byte_align loc = w’ >> rw[] *)
(* QED *)

(*/
  ffi skip test
 *)

val ffi_ast = parse_pancake ‘
fun fn() {
  #f1(2, 0, 0, 0);
  #f2(0, 0, @base, 1);
  if (ldb @base) == 0 {
    #f3(3, 0, 0, 0);
  } else {
    #f4(4, 0, 0, 0);
  }
}’;

Definition ffi_sem_def:
  ffi_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD ^ffi_ast) s
End

(* Inductive walk: *)
(* [~Tau:] (∀t. (walk t responses result ⇒ walk (Tau t) responses result)) ∧ *)
(* [~Vis:] (∀k e r. walk (k r) responses result *)
(*            ⇒ walk (Vis e k) (r::responses) ((e,r)::result)) ∧ *)
(* [~Ret:] (∀r. walk (Ret r) [] []) *)
(* End *)

(* TODO simp for future_safe_cases *)
Inductive next:
  (P (Ret r) ⇒ next P (Ret r)) ∧
  (P (Tau t) ⇒ next P t) ∧
  ((∀a. P (k a)) ⇒ next P (Vis e k))
End

(* RTC of above: AF in CTL *)
Inductive future:
  (P t ⇒ future P t) ∧
  (future P t ⇒ future P (Tau t)) ∧
  (∀a. future P (k a) ⇒ future P (Vis e k))
End

(* future but with assumption that bytes written back fit in the passed array *)
Inductive future_safe:
  (P t ⇒ future_safe P t) ∧
  (future_safe P t ⇒ future_safe P (Tau t)) ∧
  ((∀a outcome new_ffi new_bytes.
     (a = FFI_final outcome ∨
      a = FFI_return new_ffi new_bytes ∧ (LENGTH new_bytes ≤ LENGTH array))
        ⇒ future_safe P (k a))
   ⇒ future_safe P (Vis (FFI_call s conf array) k))
End

(* TODO why does this simp not work under ctx. no Taus in statements *)
Theorem future_safe_ignore_tau[simp]:
  (∀(t' : (α ffi_result, sem_vis_event, 8 result option) itree).
     ¬P (Tau t')) ⇒ (future_safe P (Tau t) ⇔ future_safe P t)
Proof
  rw[] >>
  rw[Once future_safe_cases]
QED

Definition ffi_pred_def:
  ffi_pred t =
  ((∃k k' uninit.
      (t = Vis (FFI_call "f2" [] [uninit]) k) ∧
      k (FFI_return ARB [1w : 8 word]) ≈ (Vis (FFI_call "f4" [] []) k')) ∨
   (∃outcome. t = Ret (SOME (FinalFFI outcome))))
End

Theorem ffi_pred_notau:
  ¬ffi_pred (Tau (t : (α ffi_result, sem_vis_event, 8 result option) itree))
Proof
  rw[ffi_pred_def]
QED

(* byte_align means align (word in bytes) to implicit bit-sized k-word *)
(* assume all (8-bit) byte-aligned accesses allowed, as in C *)
(* assume infinite address space *)
(* assume base memory initially contains some arbitrary word *)
Theorem ffi_sem_thm:
  (∀(b : word8). byte_align b = b) ⇒
  (∀(w : word8). w ∈ s.memaddrs) ⇒
  (∃uninitb. s.memory s.base_addr = Word uninitb) ⇒
  future_safe ffi_pred (ffi_sem s)
Proof
  rw[ffi_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  assume_tac (GEN_ALL ffi_pred_notau) >>
  (* Seq rw[seq_thm] *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_seq_def] >>
  rw[Once itree_iter_thm, Once itree_bind_thm] >>
  (* extcall *)
  qmatch_goalsub_abbrev_tac
  ‘bind (h_prog_rule_ext_call «f1» (Const 2w) (Const 0w) (Const 0w) (Const 0w) s)
   prog’ >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[miscTheory.read_bytearray_def] >>
  rw[Once future_safe_cases] >> disj2_tac >>
  (* massaging *)
  rpt strip_tac >-
   (qunabbrev_tac ‘prog’ >>
    rw[Once future_safe_cases] >>
    rw[ffi_pred_def]) >>
  qunabbrev_tac ‘prog’ >> rw[] >>
  (* second seq *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_seq_def] >>
  rw[Once itree_iter_thm, Once itree_bind_thm] >>
  qmatch_goalsub_abbrev_tac ‘bind (h_prog_rule_ext_call _ _ _ _ _ _) kprog’ >>
  (* extcall *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[miscTheory.read_bytearray_def] >>
  rw[panSemTheory.write_bytearray_def] >>
  PURE_REWRITE_TAC[ONE] >> (* wtf *)
  rw[Once $ cj 2 miscTheory.read_bytearray_def] >>
  rw[mem_load_byte_def] >>
  rw[miscTheory.read_bytearray_def] >>
  (* found tree *)
  rw[Once future_safe_cases] >> disj1_tac >>
  rw[ffi_pred_def] >>
  qunabbrev_tac ‘kprog’ >> rw[] >>
  (* cond *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
  rw[eval_def, asmTheory.word_cmp_def] >>
  qpat_abbrev_tac ‘stat = (SOME Error, s with <| memory := _; ffi := _ |>)’ >>
  rw[write_bytearray_def] >>
  rw[mem_store_byte_def] >>
  rw[mem_load_byte_def] >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  simp[byteTheory.get_byte_set_byte] >>
  (* third call happens *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[miscTheory.read_bytearray_def] >>
  metis_tac[itree_wbisim_refl]
QED

(*/ loops work!
   manual loop unrolling isn't too bad with equational rewrites
 *)

val loop_ast = parse_pancake ‘
fun fn() {
  var x = 0;
  #getnum(0, 0, @base, 1);
  while (x < (ldb @base)) {
     #ffi(0, 0, 0, 0);
     x = x + 1;
  }
}’;

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
