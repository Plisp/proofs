(*
 * actual pancake programs. simps used here.
 * properties needed for verification
 * - describing trees given arbitrary restrictions on ffi responses
 * - spec must be transparently related to the (correct) result of itree_evaluate
 * - skipping 'uninteresting' (e.g. logging) calls, optional
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

(*
Globals.max_print_depth := 18;
*)

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

Theorem apply_update_simp[simp] = cj 1 combinTheory.UPDATE_APPLY;

(*/ word nonsense
   inst type vars: INST_TYPE [gamma |-> beta, alpha |-> beta, beta |-> gamma]
   word_add_n2w
 *)

Type sem32tree[pp] = “:(β ffi_result, sem_vis_event, 32 result option) itree”;

Theorem word_resize_msb:
  1 < dimindex (:β) ∧ dimindex (:α) < dimindex (:β)
  ⇒ ¬word_msb (w2w (n : α word) : β word)
Proof
  rw[wordsTheory.word_msb_def, wordsTheory.w2w]
QED

Theorem n2w_lt:
  (0w:'a word) ≤ n2w a ∧ (0w:'a word) ≤ n2w b ∧
  a < dimword (:'a) ∧ b < dimword (:'a)
  ⇒
  ((n2w a:'a word) < (n2w b:'a word) ⇔ a < b)
Proof
  srw_tac[][wordsTheory.WORD_LESS_OR_EQ] >> fs[wordsTheory.word_lt_n2w]
QED

Theorem n2w_le:
  (0w:'a word) ≤ n2w a ∧ (0w:'a word) ≤ n2w b ∧
  a < dimword (:'a) ∧ b < dimword (:'a)
  ⇒
  ((n2w a:'a word) ≤ (n2w b:'a word) ⇔ a ≤ b)
Proof
  srw_tac[][wordsTheory.WORD_LESS_OR_EQ] >> fs[wordsTheory.word_lt_n2w]
QED

(* generalize if needed to an arbitrary list + offset *)
Theorem load_write_bytearray_thm:
  (byte_align addr = addr) ∧
  (∀(w : word32). w ∈ s.memaddrs) ∧
  (∃(k : word32). oldmem addr = Word k) ⇒
  mem_load_byte (write_bytearray addr [v] oldmem s.memaddrs s.be)
                s.memaddrs s.be addr
  = SOME v
Proof
  rw[mem_load_byte_def] >>
  rw[write_bytearray_def] >>
  rw[mem_store_byte_def] >>
  first_assum $ qspec_then ‘addr’ strip_assume_tac >>
  rw[byteTheory.get_byte_set_byte]
QED

Theorem write_bytearray_preserve_words:
  (∀w. ∃(k : word32). s.memory w = Word k) ⇒
  ∀w. ∃(k : word32). (write_bytearray loc l s.memory s.memaddrs s.be) w = Word k
Proof
  strip_tac >>
  qid_spec_tac ‘loc’ >>
  Induct_on ‘l’ >>
  rw[write_bytearray_def] >>
  fs[mem_store_byte_def] >>
  Cases_on ‘write_bytearray (loc+1w) l s.memory s.memaddrs s.be (byte_align loc)’ >>
  rw[] >>
  rw[combinTheory.APPLY_UPDATE_THM]
QED

(*/ spec combinators
   - temporal logic?
 *)

(* Inductive walk: *)
(* [~Tau:] (∀t. (walk t responses result ⇒
                 walk (Tau t) responses result)) ∧ *)
(* [~Vis:] (∀k e r. walk (k r) responses result *)
(*            ⇒ walk (Vis e k) (r::responses) ((e,r)::result)) ∧ *)
(* [~Ret:] (∀r. walk (Ret r) [] []) *)
(* End *)

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
  (∀k s conf array.
    (∀outcome. future_safe P (k (FFI_final outcome))) ∧
    (∀new_ffi new_bytes. (LENGTH new_bytes = LENGTH array) ⇒
                         future_safe P (k (FFI_return new_ffi new_bytes)))
    ⇒ future_safe P (Vis (FFI_call s conf array) k))
End

(* needs to be α for type vars to match *)
Theorem future_safe_ignore_tau[simp]:
  (∀(t' : α sem32tree). ¬P (Tau t')) ⇒ (future_safe P (Tau t) ⇔ future_safe P t)
Proof
  rw[] >> rw[Once future_safe_cases]
QED






(*/ ffi proof *)

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

Definition ffi_pred_def:
  ffi_pred (t : α sem32tree) =
  ((∃k k' uninit.
     (t = Vis (FFI_call "f2" [] [uninit]) k) ∧
     k (FFI_return ARB [1w]) ≈ (Vis (FFI_call "f4" [] []) k')) ∨
   (∃outcome. t = Ret (SOME (FinalFFI outcome))))
End

Theorem ffi_pred_notau:
  ∀(t : α sem32tree). ¬ffi_pred (Tau t)
Proof
  rw[ffi_pred_def]
QED

(* byte_align means align (word in bytes) to implicit bit-sized k-word *)
(* assume all (8-bit) byte-aligned accesses allowed, as in C *)
(* assume infinite address space: memaddrs (relax this later) *)
Theorem ffi_sem_thm:
  (∀(w : word32). w ∈ s.memaddrs) ∧
  (byte_align s.base_addr = s.base_addr) ∧
  (∃uninitb. s.memory s.base_addr = Word uninitb) ⇒
  future_safe ffi_pred (ffi_sem s)
Proof
  rw[ffi_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  assume_tac ffi_pred_notau >>
  (* Seq *)
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
  qmatch_goalsub_abbrev_tac ‘bind (h_prog_rule_ext_call _ _ _ _ _ _) kprog’ >>
  (* extcall *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[miscTheory.read_bytearray_def] >>
  rw[panSemTheory.write_bytearray_def] >>
  PURE_REWRITE_TAC[ONE] >>
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
  simp[mem_load_byte_def] >>
  simp[byteTheory.get_byte_set_byte] >>
  (* third call happens *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[miscTheory.read_bytearray_def] >>
  metis_tac[itree_wbisim_refl]
QED

(*/ loops! *)

val while_ast = parse_pancake ‘
fun fn() {
  var x = 0;
  #getc(0, 0, @base, 1);
  while (x < (ldb @base)) {
    #ffi(0, 0, 0, 0);
    x = x + 1;
  }
}’;

Definition while_sem_def:
  while_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD ^while_ast) s
End

Inductive loop_pred:
  (loop_pred (0 : num) (Ret NONE)) ∧
  (∀k. (∃vis. k (FFI_return ARB []) ≈ vis ∧ loop_pred (m-1) vis)
       ⇒ loop_pred (m : num) (Vis (FFI_call "ffi" [] []) k))
End

Theorem loop_pred_notau:
  ∀(n : num) t. ¬loop_pred n (Tau (t : α sem32tree))
Proof
  rw[Once loop_pred_cases]
QED

(* byteTheory bytes_to_word *)
Definition while_pred_def:
  while_pred t =
  ((∃k uninit.
     (t = Vis (FFI_call "getc" [] [uninit]) k) ∧
     (∀(n : word8).
        (0w : word8) < n ⇒
        ∃tl. (k (FFI_return ARB [n])) ≈ tl ∧
             future_safe (loop_pred (w2n n)) tl)) ∨
   (∃outcome. t = Ret (SOME (FinalFFI outcome)))) (* β result option *)
End

Theorem while_pred_notau:
  ¬while_pred (Tau (t : α sem32tree))
Proof
  rw[while_pred_def]
QED

Theorem future_safe_ignore_tau2[simp]:
  (∀(t' : α sem32tree). ¬P x (Tau t'))
  ⇒ (future_safe (P x) (Tau t) ⇔ future_safe (P x) t)
Proof
  rw[] >> rw[Once future_safe_cases]
QED

Theorem while_word_lem:
  i < n ∧ n < 256 ⇒ (n2w i : word32) < n2w n
Proof
  rw[] >>
  ‘(0w : word32) ≤ n2w i ∧ (0w : word32) ≤ n2w n’ suffices_by rw[n2w_lt] >>
  rw[wordsTheory.WORD_LESS_OR_EQ, miscTheory.word_lt_0w]
QED

Theorem while_sem_lem:
  (∀(w : word32). w ∈ s.memaddrs) ∧
  (byte_align s.base_addr = s.base_addr) ∧
  (s.memory s.base_addr = Word uninitb) ∧
  (∀t. ¬while_pred (Tau (t : α sem32tree))) ∧
  0 < n ∧ n < dimword (:8) ∧ i ≤ n ⇒
  ∃tl.
  to_ffi
  (iter
   (mrec_cb h_prog)
   (iter
    (λ(p',s'). h_prog_while_cb (p',s') (eval s' (Cmp Less (Var «x»)
                                                     (LoadByte BaseAddr))))
    (Seq
     (ExtCall «ffi» (Const 0w) (Const 0w) (Const 0w) (Const 0w))
     (Assign «x» (Op Add [Var «x»; Const 1w])),
     s with <|locals := s.locals |+ («x»,ValWord (n2w i));
              memory := write_bytearray s.base_addr [n2w n] s.memory
                                        s.memaddrs s.be; ffi := ARB|>)))
  ≈ tl
  ∧ future_safe (loop_pred (n - i)) tl
Proof
  rw[Once future_safe_cases] >>
  dsimp[] >> disj1_tac >>
  Induct_on ‘n - i’ >-
   (strip_tac >> strip_tac >> strip_tac >>
    pop_assum $ assume_tac o GSYM >> rw[] >>
    rw[Once itree_iter_thm, Once itree_iter_thm] >>
    rw[GSYM itree_iter_thm] >>
    rw[Once eval_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    simp[Once eval_def, load_write_bytearray_thm, asmTheory.word_cmp_def] >>
    fs[] >>
    simp[wordsTheory.w2w_def] >>
    ‘i = n’ by rw[] >>
    rw[] >> qexists_tac ‘Ret NONE’ >>
    simp[itree_wbisim_refl, Once future_safe_cases, Once loop_pred_cases]) >>
  rw[Once itree_iter_thm, Once itree_iter_thm] >>
  rw[GSYM itree_iter_thm] >>
  rw[Once eval_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[Once eval_def, load_write_bytearray_thm, asmTheory.word_cmp_def] >>
  simp[wordsTheory.w2w_def] >>
  ‘i < n’ by rw[] >>
  ‘(n2w i : word32) < n2w n’ by rw[while_word_lem] >> rw[] >>
  rw[h_prog_def, h_prog_rule_seq_def] >>
  rw[h_prog_rule_ext_call_def] >>
  rw[miscTheory.read_bytearray_def] >>
  qmatch_goalsub_abbrev_tac ‘thing ≈ _ ∧ _’ >>
  qexists_tac ‘thing’ >> rw[itree_wbisim_refl] >>
  qunabbrev_tac ‘thing’ >>
  rw[Once loop_pred_cases] >>
  rw[h_prog_def, h_prog_rule_assign_def] >>
  rw[Once eval_def, finite_mapTheory.FLOOKUP_UPDATE,
     wordLangTheory.word_op_def, is_valid_value_def, shape_of_def] >>
  rw[Once panSemTheory.write_bytearray_def] >>
  first_x_assum $ qspecl_then [‘n’, ‘i + 1’] strip_assume_tac >>
  gvs[] >>
  qexists_tac ‘tl’ >>
  ‘n2w (i + 1) = (n2w i) + (1w : word32)’ by rw[wordsTheory.word_add_n2w] >>
  fs[]
QED

Theorem while_sem_thm:
  (∀(w : word32). w ∈ s.memaddrs) ∧
  (byte_align s.base_addr = s.base_addr) ∧
  (∃uninitb. s.memory s.base_addr = Word uninitb) ⇒
  future_safe while_pred (while_sem s)
Proof
  rw[while_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  assume_tac (GEN_ALL while_pred_notau) >>
  ‘eval s (Const 0w) = SOME (ValWord 0w)’ by rw[eval_def] >>
  drule dec_lifted >> rw[] >> pop_assum kall_tac >> pop_assum kall_tac >>
  (* seq *)
  rw[seq_thm] >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[miscTheory.read_bytearray_def] >>
  PURE_REWRITE_TAC[ONE] >>
  rw[miscTheory.read_bytearray_def] >>
  rw[mem_load_byte_def] >>
  rw[Once future_safe_cases] >> disj1_tac >>
  rw[while_pred_def] >>
  rw[h_prog_rule_while_alt] >>
  Cases_on ‘n’ >>
  ‘w2n (n2w n' : word8) = n' - 0’ by rw[wordsTheory.w2n_n2w] >>
  drule (INST_TYPE [gamma |-> alpha] while_sem_lem) >> rw[] >>
  pop_assum $ qspecl_then [‘n'’, ‘0’] strip_assume_tac >>
  fs[wordsTheory.WORD_LT]
QED

(*/ real *)

val muxrx_ast = parse_pancake ‘
fun fn() {
  var drv_dequeue_c = @base;
  var drv_dequeue_a = @base + 1;
  #drv_dequeue_used(drv_dequeue_c, 1, drv_dequeue_a, 1);
  var drv_dequeue_ret = ldb drv_dequeue_c;
  var got_char = ldb drv_dequeue_a;

  if drv_dequeue_ret != 0 {
      return 1;
  }

  // Get the current status of the escape character from the ffi file

  var escape_character_a = @base + 3;
  #get_escape_character(0,0,escape_character_a, 1);
  var escape_character = ldb escape_character_a;

  if escape_character == 1 {
      // give the char to the client, previous character was an escape character
      #escape_1(0,0,0,0);

      var client_a = @base + 4;
      #get_client(0, 0, client_a, 1);
      var client = ldb client_a;

      // Check that we have requests by this client to get a char

      var check_num_to_get_chars_a = @base + 5;
      #check_num_to_get_chars(0, 0, check_num_to_get_chars_a, 1);
      var num_to_get_chars_ret = ldb check_num_to_get_chars_a;

      if num_to_get_chars_ret == 0 {
          return 0;
      }

      // Batch the dequeue and enqueue into the client's rings

      var cli_dequeue_enqueue_c = @base + 6;
      var cli_dequeue_enqueue_a = @base + 8;
      strb cli_dequeue_enqueue_c, client;
      strb cli_dequeue_enqueue_c + 1, got_char;
      #batch_cli_dequeue_enqueue(cli_dequeue_enqueue_c,2, cli_dequeue_enqueue_a,1);

      var set_escape_character_c = @base + 9;
      strb set_escape_character_c, 0;
      #set_escape_character(set_escape_character_c, 1, 0, 0);

      return 0;
  }

  if escape_character == 2 {
      // The previous character was "@". Switch input to a new client.
      #escape_2(0,0,0,0);

      var new_client = got_char - 48;
      if new_client >= 1 {
          var get_num_clients_a = @base + 4;
          #get_num_clients(0,0,get_num_clients_a, 1);
          var num_clients = ldb get_num_clients_a;

          if new_client <= num_clients {
              var set_client_c = @base + 5;
              strb set_client_c, new_client;
              #set_client(set_client_c, 1, 0, 0);
          }
      }

      var set_escape_character_c = @base + 9;
      strb set_escape_character_c, 0;
      #set_escape_character(set_escape_character_c, 1, 0, 0);

      return 0;
  }

  if escape_character == 0 {
      // No escape character has been set
      #escape_0(0,0,0,0);

      // Ascii for '\'
      if got_char == 92 {
          #escape_case(0,0,0,0);
          var set_escape_character_c = @base + 9;
          strb set_escape_character_c, 1;
          #set_escape_character(set_escape_character_c, 1, 0, 0);

          return 0;
      }

      // Ascii for '@'
      if got_char == 64 {
          #at_case(0,0,0,0);
          var set_escape_character_c = @base + 9;
          strb set_escape_character_c, 2;
          #set_escape_character(set_escape_character_c, 1, 0, 0);

          return 0;
      }

      // Otherwise we just want to give the client the character

      var client_a = @base + 4;
      #get_client(0, 0, client_a, 1);
      var client = ldb client_a;

      // Check that we have requests by this client to get a char

      var check_num_to_get_chars_a = @base + 5;
      #check_num_to_get_chars(0, 0, check_num_to_get_chars_a, 1);
      var num_to_get_chars_ret = ldb check_num_to_get_chars_a;

      if num_to_get_chars_ret == 0 {
          return 0;
      }

      // Batch the dequeue and enqueue into the client's rings

      var cli_dequeue_enqueue_c = @base + 6;
      var cli_dequeue_enqueue_a = @base + 8;
      strb cli_dequeue_enqueue_c, client;
      strb cli_dequeue_enqueue_c + 1, got_char;
      #batch_cli_dequeue_enqueue(cli_dequeue_enqueue_c,2, cli_dequeue_enqueue_a,1);

      var set_escape_character_c = @base + 9;
      strb set_escape_character_c, 0;
      #set_escape_character(set_escape_character_c, 1, 0, 0);

      return 0;
  }
  return 0;
}’;

Definition muxrx_sem_def:
  muxrx_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD ^muxrx_ast) s
End
