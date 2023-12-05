(*
 * actual pancake programs. simps used here.
 * properties needed for verification
 * - describing trees given arbitrary restrictions on ffi responses
 * - spec must be transparently related to the (correct) result of itree_evaluate
 * - skipping 'irrelevant' (e.g. logging) calls, optional
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
Theorem do_flookup_simp[simp] = finite_mapTheory.FLOOKUP_UPDATE;
Theorem read_bytearray_0[simp] = cj 1 miscTheory.read_bytearray_def;
Theorem write_bytearray_0[simp] = cj 1 write_bytearray_def;
Theorem read_bytearray_1:
  read_bytearray addr 1 getter =
  (case getter addr of NONE => NONE | SOME b => SOME [b])
Proof
  PURE_REWRITE_TAC[ONE] >>
  rw[miscTheory.read_bytearray_def]
QED

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

Theorem load_write_bytearray_thm2:
  (∀(w : word32). w ∈ s.memaddrs) ∧
  (∃(k : word32). oldmem (byte_align addr) = Word k) ⇒
  mem_load_byte (write_bytearray addr [v] oldmem s.memaddrs s.be)
                s.memaddrs s.be addr
  = SOME v
Proof
  rw[mem_load_byte_def] >>
  rw[write_bytearray_def] >>
  rw[mem_store_byte_def] >>
  rw[byteTheory.get_byte_set_byte]
QED

Theorem load_write_bytearray_other:
  (∀(w : word32). w ∈ s.memaddrs) ∧
  (∃(k : word32). smem (byte_align addr) = Word k) ∧
  (∃(k : word32). smem (byte_align other) = Word k) ⇒
  other ≠ addr ⇒
  mem_load_byte (write_bytearray other [c] smem s.memaddrs s.be)
                s.memaddrs s.be addr
  = mem_load_byte smem s.memaddrs s.be addr
Proof
  rw[mem_load_byte_def] >>
  rw[write_bytearray_def] >>
  rw[mem_store_byte_def] >>
  Cases_on ‘byte_align addr = byte_align other’ >>
  rw[] >-
   (‘k = k'’ by fs[] >>
    gvs[] >>
    irule miscTheory.get_byte_set_byte_diff >>
    rw[] >> EVAL_TAC) >>
  rw[combinTheory.UPDATE_APPLY]
QED

Theorem write_bytearray_preserve_words[simp]:
  oldmem (byte_align w) = Word k ⇒
  ∃(k : word32). (write_bytearray loc l oldmem s.memaddrs s.be) (byte_align w)
                 = Word k
Proof
  strip_tac >>
  qid_spec_tac ‘loc’ >>
  Induct_on ‘l’ >>
  rw[write_bytearray_def] >>
  fs[mem_store_byte_def] >>
  Cases_on ‘write_bytearray (loc+1w) l oldmem s.memaddrs s.be (byte_align loc)’ >>
  rw[] >>
  rw[combinTheory.APPLY_UPDATE_THM]
QED

Theorem baseaddr_ref[simp]:
  to_ffi (itree_mrec h_prog ((Dec name BaseAddr p), s))
  = Tau (to_ffi
         (itree_mrec h_prog
                     (p,s with locals
                        := s.locals |+ (name,ValWord s.base_addr)))) ∧
  to_ffi (itree_mrec h_prog ((Dec name (Op Add [BaseAddr; Const k]) p), s))
  = Tau (to_ffi
         (itree_mrec h_prog
                     (p,s with locals
                        := s.locals |+ (name,ValWord (s.base_addr + k)))))
Proof
  CONJ_TAC >-
   (‘eval s BaseAddr = SOME (ValWord s.base_addr)’ by rw[eval_def] >>
    drule dec_lifted >> rw[]) >>
  ‘eval s (Op Add [BaseAddr; Const k]) = SOME (ValWord (s.base_addr + k))’
    by rw[eval_def, wordLangTheory.word_op_def] >>
  drule dec_lifted >> rw[]
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
  ((∀a. future P (k a)) ⇒ future P (Vis e k))
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

(*/ real
   TODO there's a semantic error caused by loading from drv_dequeue_c, read-only
 *)

val muxrx_ast = parse_pancake ‘
fun fn() {
  var drv_dequeue_c = @base;
  var drv_dequeue_a = @base + 1;
  #drv_dequeue_used(drv_dequeue_c, 1, drv_dequeue_a, 1);
  (* var drv_dequeue_ret = ldb drv_dequeue_c; *)
 var got_char = ldb drv_dequeue_a;
  (* if drv_dequeue_ret != 0 { return 1; } *)

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
      strb set_escape_character_c, 0; // escape off
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
          strb set_escape_character_c, 1; // escape
         #set_escape_character(set_escape_character_c, 1, 0, 0);

         return 0;
      }

      // Ascii for '@'
      if got_char == 64 {
          #at_case(0,0,0,0);
          var set_escape_character_c = @base + 9;
          strb set_escape_character_c, 2; // escape @
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

(* assumption: zero parameter means we get no bytes written, so [] *)
Definition mux_backslash_pred_def:
  mux_backslash_pred t =
  ((∃k. t = Vis (FFI_call "set_escape_character" [0w : word8] []) k ∧
        future_safe (λt. t = Ret (SOME (Return (ValWord 0w))))
                    (k (FFI_return ARB [])))
   ∨ (t = Ret (SOME (Return (ValWord 0w))))
   ∨ ∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem mux_backslash_pred_notau:
  ¬mux_backslash_pred (Tau (t : α sem32tree))
Proof
  rw[mux_backslash_pred_def]
QED

Definition muxrx_pred_def:
  muxrx_pred t =
  ∀c.
  (∃k1 k2 uninit1 uninit2 uninit.
    (t = Vis (FFI_call "drv_dequeue_used" [uninit1] [uninit2]) k1) ∧
    (k1 (FFI_return ARB [c]) ≈
        Vis (FFI_call "get_escape_character" [] [uninit]) k2) ∧
    (* backslash escape case, transitions to zero *)
    future_safe mux_backslash_pred (k2 (FFI_return ARB [1w]))
  ) ∨
  (∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem muxrx_pred_notau:
  ¬muxrx_pred (Tau (t : α sem32tree))
Proof
  rw[muxrx_pred_def, mux_backslash_pred_def]
QED

(* the proof *)

Theorem mux_pred_implies_SOME_leaf:
  future_safe mux_backslash_pred tl ⇒
  future_safe (λt. ∃r. t = Ret (SOME r)) tl
Proof
  qid_spec_tac ‘tl’ >>
  ho_match_mp_tac future_safe_ind >>
  rw[Once future_safe_cases] >-
   (gvs[mux_backslash_pred_def] >>
    rw[Once future_safe_cases]) >-
   (rw[Once future_safe_cases]) >-
   (rw[Once future_safe_cases] >>
    pop_last_assum $ qspec_then ‘outcome’ strip_assume_tac >>
    rw[Once future_safe_cases])
QED

(* TODO make this simp automatically compute FLOOKUP *)
Theorem dec_loadbyte:
  FLOOKUP s.locals name = SOME (ValWord loc) ⇒
  s.memory (byte_align loc) = Word w ⇒
  (∀w. w ∈ s.memaddrs)
  ⇒ to_ffi (itree_mrec h_prog ((Dec vname (LoadByte (Var name)) p), s))
    = Tau
      (to_ffi
       (itree_mrec
        h_prog
        (p, s with
              locals := s.locals |+ (vname,ValWord (w2w (get_byte loc w s.be))))))
Proof
  rw[] >>
  ‘eval s (LoadByte (Var name)) = SOME (ValWord (w2w (get_byte loc w s.be)))’
    by rw[eval_def, mem_load_byte_def] >>
  drule dec_lifted >> rw[]
QED

Theorem muxrx_correct:
  (∀(w : word32). w ∈ s.memaddrs) ∧
  (byte_align s.base_addr = s.base_addr) ∧
  (byte_align (s.base_addr + 1w) = s.base_addr) ∧
  (byte_align (s.base_addr + 3w) = s.base_addr) ∧
  (byte_align (s.base_addr + 4w) = s.base_addr) ∧
  (byte_align (s.base_addr + 5w) = s.base_addr) ∧
  (byte_align (s.base_addr + 6w) = s.base_addr) ∧
  (byte_align (s.base_addr + 7w) = s.base_addr) ∧
  (byte_align (s.base_addr + 8w) = (s.base_addr + 8w)) ∧
  (byte_align (s.base_addr + 9w) = (s.base_addr + 8w)) ∧
  (∃uninitb. s.memory s.base_addr = Word uninitb) ∧
  (∃uninitb. s.memory (s.base_addr + 8w) = Word uninitb) ∧
  (∃uninitb.
    mem_load_byte s.memory s.memaddrs s.be (s.base_addr + 3w) = SOME uninitb) ∧
  (∃uninitb.
    mem_load_byte s.memory s.memaddrs s.be (s.base_addr + 4w) = SOME uninitb) ∧
  (∃uninitb.
    mem_load_byte s.memory s.memaddrs s.be (s.base_addr + 5w) = SOME uninitb) ∧
  (∃uninitb.
    mem_load_byte s.memory s.memaddrs s.be (s.base_addr + 8w) = SOME uninitb) ∧
  (∃uninitb.
    mem_load_byte s.memory s.memaddrs s.be (s.base_addr + 9w) = SOME uninitb)
  ⇒
  future_safe muxrx_pred (muxrx_sem s)
Proof
  rw[muxrx_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  assume_tac (GEN_ALL muxrx_pred_notau) >>
  rw[seq_thm] >>
  qmatch_goalsub_abbrev_tac ‘(bind _ rest)’ >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[read_bytearray_1, mem_load_byte_def] >>
  rw[Once future_safe_cases] >> disj1_tac >>
  rw[muxrx_pred_def] >>
  qunabbrev_tac ‘rest’ >> rw[] >>
  qmatch_goalsub_abbrev_tac ‘itree_mrec _ (_,st)’ >>
  subgoal ‘eval st (LoadByte (Var «drv_dequeue_a»)) = SOME (ValWord (w2w c))’ >-
   (qunabbrev_tac ‘st’ >> rw[eval_def] >> rw[load_write_bytearray_thm2]) >>
  drule dec_lifted >> rw[] >> pop_assum kall_tac >> pop_assum kall_tac >>
  (* get_escape_character *)
  rw[seq_thm] >>
  qmatch_goalsub_abbrev_tac ‘(bind _ rest)’ >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[read_bytearray_1] >>
  qunabbrev_tac ‘st’ >> rw[] >>
  rw[load_write_bytearray_other] >>
  (* get_escape_char *)
  qmatch_goalsub_abbrev_tac ‘Vis _ k2’ >>
  qexistsl_tac [‘k2’, ‘uninitb''’] >>
  rw[itree_wbisim_refl] >>
  qunabbrev_tac ‘k2’ >> qunabbrev_tac ‘rest’ >>
  assume_tac (GEN_ALL mux_backslash_pred_notau) >>
  rw[] >>
  ‘∃k. (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
       (byte_align (s.base_addr + 3w)) = Word k’
    by rw[write_bytearray_preserve_words] >>
  qmatch_goalsub_abbrev_tac ‘itree_mrec _ (_,st)’ >>

  subgoal ‘eval st (LoadByte (Var «escape_character_a»)) = SOME (ValWord 1w)’ >-
   (qunabbrev_tac ‘st’ >> rw[eval_def] >>
    ‘∃k. (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
         (byte_align (s.base_addr + 3w)) = Word k’
      by rw[write_bytearray_preserve_words] >>
    rw[load_write_bytearray_thm2]) >>
  drule dec_lifted >> rw[] >> pop_assum kall_tac >> pop_assum kall_tac >>
  rw[seq_thm] >>
  (* if the first bind (if-branch) returns we're done *)
  qmatch_goalsub_abbrev_tac ‘to_ffi (bind if1 rest)’ >>
  ‘future_safe mux_backslash_pred (to_ffi if1)’ suffices_by cheat >>
  qunabbrev_tac ‘if1’ >> pop_assum kall_tac >>
  (* questionable stuff done *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
  rw[Once eval_def, asmTheory.word_cmp_def] >>
  rw[GSYM itree_mrec_alt, seq_thm] >>
  (* escape_1 *)
  rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[Once future_safe_cases] >> disj2_tac >>
  rw[] >-
   (rw[Once future_safe_cases, mux_backslash_pred_def]) >>
  rw[seq_thm] >>
  (* get_client *)
  rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[read_bytearray_1] >>
  ‘∃k. (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
       (byte_align (s.base_addr + 4w)) = Word k’
    by rw[write_bytearray_preserve_words] >>
  subgoal ‘mem_load_byte st.memory st.memaddrs st.be (st.base_addr + 4w)
           = SOME uninitb'³'’ >-
   (qunabbrev_tac ‘st’ >> rw[load_write_bytearray_other]) >>
  (* vis *)
  rw[Once future_safe_cases] >> disj2_tac >>
  rw[] >-
   (rw[Once future_safe_cases, mux_backslash_pred_def]) >>
  Cases_on ‘new_bytes’ >> fs[] >> pop_assum kall_tac >>
  pop_assum kall_tac >>
  ‘∃k. (write_bytearray (s.base_addr + 3w) [1w]
                        (write_bytearray (s.base_addr + 1w) [c] s.memory
                                         s.memaddrs s.be) s.memaddrs s.be)
       (byte_align (s.base_addr + 4w)) = Word k’
    by rw[write_bytearray_preserve_words] >>
  qmatch_goalsub_abbrev_tac ‘itree_mrec _ (_,st2)’ >>
  (* got client = h *)
  subgoal ‘eval st2 (LoadByte (Var «client_a»)) = SOME (ValWord (w2w h))’ >-
   (qunabbrev_tac ‘st2’ >> qunabbrev_tac ‘st’ >>
    fs[eval_def] >>
    rw[load_write_bytearray_thm2]) >>
  drule dec_lifted >> rw[] >> pop_assum kall_tac >> pop_assum kall_tac >>
  (* check_num_to_chars TODO what this simp worked? *)
  (*‘eval st2 (Op Add [BaseAddr;Const 5w]) = SOME (ValWord (st2.base_addr + 5w))’ *)
  (*   by rw[base_addr_offset] >> *)
  (* drule dec_lifted >> rw[] >> pop_assum kall_tac >> *)
  rw[seq_thm] >>
  rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[read_bytearray_1] >>
  (* ‘(s.base_addr + 4w) ≠ (s.base_addr + 5w)’ by rw[] >> *)
  ‘∃k. (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
       (byte_align (s.base_addr + 5w)) = Word k’
    by rw[write_bytearray_preserve_words] >>
  ‘∃k. (write_bytearray (s.base_addr + 3w) [1w]
                        (write_bytearray (s.base_addr + 1w)
                                         [c] s.memory s.memaddrs s.be)
                        s.memaddrs s.be)
       (byte_align (s.base_addr + 5w)) = Word k’
    by rw[write_bytearray_preserve_words] >>
  rw[load_write_bytearray_other] >>
  (* ‘(s.base_addr + 3w) ≠ (s.base_addr + 5w)’ by rw[] >> *)
  ‘∃k. (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
       (byte_align (s.base_addr + 5w)) = Word k’
    by rw[write_bytearray_preserve_words] >>
  (* load_write_bytearray_other twice *)
  subgoal ‘mem_load_byte st2.memory st2.memaddrs st2.be (st2.base_addr + 5w)
           = SOME uninitb'⁴'’ >-
   (qunabbrev_tac ‘st2’ >> qunabbrev_tac ‘st’ >> fs[] >>
    rw[load_write_bytearray_other]) >>
  rw[] >>
  (* ffi check_num_to_get_chars, h' return *)
  rw[Once future_safe_cases] >> disj2_tac >>
  rw[] >-
   (rw[Once future_safe_cases, mux_backslash_pred_def]) >>
  Cases_on ‘new_bytes’ >> fs[] >> pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac ‘itree_mrec _ (_,st3)’ >>
  subgoal ‘eval st3 (LoadByte (Var «check_num_to_get_chars_a»))
           = SOME (ValWord (w2w h'))’ >-
   (qunabbrev_tac ‘st3’ >> qunabbrev_tac ‘st2’ >> qunabbrev_tac ‘st’ >>
    fs[eval_def] >>
    ‘∃k. (write_bytearray
          (s.base_addr + 4w) [h]
          (write_bytearray
           (s.base_addr + 3w) [1w]
           (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
           s.memaddrs s.be)
          s.memaddrs s.be)
         (byte_align (s.base_addr + 5w)) = Word k’
      by rw[write_bytearray_preserve_words] >>
    rw[load_write_bytearray_thm2]) >>
  drule dec_lifted >> rw[] >> pop_assum kall_tac >> pop_assum kall_tac >>

  rw[seq_thm] >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
  rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >-
   (rw[h_prog_def, h_prog_rule_return_def,
       panLangTheory.size_of_shape_def, shape_of_def] >>
    rw[Once future_safe_cases, mux_backslash_pred_def]) >>
  rw[h_prog_def] >> pop_assum kall_tac >>
  (* after if 0 *)
  rw[GSYM itree_mrec_alt, GSYM h_prog_def] >>
  rw[seq_thm] >>
  (* store byte from client in arg *)
  qmatch_goalsub_abbrev_tac ‘(bind _ rest)’ >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_store_byte_def] >>
  subgoal ‘FLOOKUP st3.locals «client» = SOME (ValWord (w2w h))’ >-
   (qunabbrev_tac ‘st3’ >> rw[finite_mapTheory.FLOOKUP_UPDATE]) >>
  rw[] >>
  subgoal
  ‘mem_store_byte st3.memory st3.memaddrs st3.be
   (st3.base_addr + 6w) (w2w (w2w h : word32))
   = SOME
     s.memory⦇
     s.base_addr ↦
     Word
     (set_byte (s.base_addr + 6w) (w2w (w2w h : word32))
               (set_byte (s.base_addr + 5w) h'
                         (set_byte (s.base_addr + 4w) h
                                   (set_byte (s.base_addr + 3w) 1w
                                             (set_byte (s.base_addr + 1w)
                                                       c uninitb
                                                       s.be) s.be) s.be) s.be) s.be)
          ⦈’ >-
   (qunabbrev_tac ‘st3’ >> qunabbrev_tac ‘st2’ >> qunabbrev_tac ‘st’ >>
    fs[mem_store_byte_def, write_bytearray_def]) >>
  rw[] >>
  qunabbrev_tac ‘rest’ >> rw[] >> qmatch_goalsub_abbrev_tac ‘(bind _ rest)’ >>
  qmatch_goalsub_abbrev_tac ‘itree_mrec _ (_,st4)’ >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_store_byte_def] >>
  subgoal ‘eval st4 (Op Add [Var «cli_dequeue_enqueue_c»; Const 1w])
           = SOME (ValWord (st3.base_addr + 7w))’ >-
   (qunabbrev_tac ‘st4’ >> qunabbrev_tac ‘st3’ >>
    rw[eval_def, wordLangTheory.word_op_def]) >>
  rw[] >> pop_assum kall_tac >>
  subgoal ‘FLOOKUP st4.locals «got_char» = SOME (ValWord (w2w c))’ >-
   (qunabbrev_tac ‘st4’ >> qunabbrev_tac ‘st3’ >> qunabbrev_tac ‘st2’ >>
    qunabbrev_tac ‘st’ >> rw[]) >>
  rw[] >>
  subgoal
  ‘mem_store_byte st4.memory st4.memaddrs st4.be
   (st3.base_addr + 7w) (w2w (w2w c : word32)) =
   SOME
   s.memory⦇
   s.base_addr ↦
   Word
   (set_byte (s.base_addr + 7w) (w2w (w2w c : word32))
             (set_byte (s.base_addr + 6w) (w2w (w2w h : word32))
                       (set_byte (s.base_addr + 5w) h'
                                 (set_byte (s.base_addr + 4w) h
                                           (set_byte (s.base_addr + 3w) 1w
                                                     (set_byte (s.base_addr + 1w)
                                                               c uninitb
                                                               s.be)
                                                     s.be) s.be) s.be) s.be) s.be)
          ⦈’ >-
   (qunabbrev_tac ‘st4’ >> qunabbrev_tac ‘st3’ >> qunabbrev_tac ‘st2’ >>
    qunabbrev_tac ‘st’ >> fs[mem_store_byte_def, write_bytearray_def]) >>
  qunabbrev_tac ‘rest’ >> rw[] >> qmatch_goalsub_abbrev_tac ‘(bind _ rest)’ >>
  (* extcall batch_cli_deq/enq *)
  rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  subgoal ‘FLOOKUP st4.locals «cli_dequeue_enqueue_c» =
           SOME (ValWord (st3.base_addr + 6w))’ >-
   (qunabbrev_tac ‘st4’ >> rw[]) >>
  rw[] >>
  subgoal ‘FLOOKUP st4.locals «cli_dequeue_enqueue_a» =
           SOME (ValWord (st3.base_addr + 8w))’ >-
   (qunabbrev_tac ‘st4’ >> rw[]) >>
  rw[] >>
  subgoal
  ‘read_bytearray (st3.base_addr + 6w) 2
   (mem_load_byte
    s.memory⦇
    s.base_addr ↦
    Word
    (set_byte (s.base_addr + 7w) (w2w (w2w c : word32))
              (set_byte (s.base_addr + 6w)
                        (w2w (w2w h : word32))
                        (set_byte (s.base_addr + 5w) h'
                                  (set_byte (s.base_addr + 4w) h
                                            (set_byte (s.base_addr + 3w) 1w
                                                      (set_byte (s.base_addr + 1w)
                                                                c uninitb s.be)
                                                      s.be) s.be)
                                  s.be) s.be) s.be)
                           ⦈ st4.memaddrs st4.be)
   = SOME [w2w (w2w h : word32) ; w2w (w2w c : word32)]’ >-
   (cheat
    (* PURE_REWRITE_TAC[TWO] >> PURE_REWRITE_TAC[ONE]*)
   ) >>
  rw[] >>
  PURE_REWRITE_TAC[ONE] >>
  ‘(byte_align (st3.base_addr + 8w)) = (byte_align (s.base_addr + 8w))’ by cheat >>
  ‘s.base_addr ≠ (s.base_addr + 8w)’ by cheat >>
  rw[miscTheory.read_bytearray_def, mem_load_byte_def, combinTheory.UPDATE_APPLY] >>
  rw[Once future_safe_cases] >> disj2_tac >>
  rw[] >-
   (qunabbrev_tac ‘rest’ >> rw[Once future_safe_cases, mux_backslash_pred_def]) >>
  qunabbrev_tac ‘rest’ >>
  Cases_on ‘new_bytes’ >> fs[] >> pop_assum kall_tac >>
  rw[GSYM itree_mrec_alt, GSYM h_prog_def] >>
  rw[seq_thm] >>
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_store_byte_def] >>
  subgoal
  ‘write_bytearray (st3.base_addr + 8w) [h'']
   s.memory⦇
   s.base_addr ↦
   Word
   (set_byte (s.base_addr + 7w) (w2w (w2w c : word32))
             (set_byte (s.base_addr + 6w) (w2w (w2w h : word32))
                       (set_byte (s.base_addr + 5w) h'
                                 (set_byte (s.base_addr + 4w) h
                                           (set_byte (s.base_addr + 3w) 1w
                                                     (set_byte (s.base_addr + 1w) c
                                                               uninitb s.be) s.be)
                                           s.be)
                                 s.be) s.be) s.be)
           ⦈
           st4.memaddrs st4.be
           (byte_align (st4.base_addr + 9w)) =
   s.memory⦇
   s.base_addr + 8w ↦ Word (set_byte (st3.base_addr + 8w) h'' uninitb' st4.be);
   s.base_addr ↦
    Word
    (set_byte (s.base_addr + 7w) (w2w (w2w c : word32))
              (set_byte (s.base_addr + 6w) (w2w (w2w h : word32))
                        (set_byte (s.base_addr + 5w) h'
                                  (set_byte (s.base_addr + 4w) h
                                            (set_byte (s.base_addr + 3w) 1w
                                                      (set_byte (s.base_addr + 1w)
                                                                c uninitb s.be)
                                                      s.be) s.be) s.be) s.be) s.be)
        ⦈ (byte_align (st4.base_addr + 9w))’ >-
   (qunabbrev_tac ‘st4’ >> qunabbrev_tac ‘st3’ >> qunabbrev_tac ‘st2’ >>
    qunabbrev_tac ‘st’ >>
    fs[mem_store_byte_def, write_bytearray_def, combinTheory.UPDATE_APPLY]) >>
  ‘(byte_align (st4.base_addr + 9w)) = (byte_align (s.base_addr + 9w))’ by cheat >>
  rw[] >>
  rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  qmatch_goalsub_abbrev_tac  ‘iter _ (_ test _ _)’ >>
  subgoal
  ‘test =
  SOME (s.memory⦇
          s.base_addr + 8w ↦ Word (set_byte (s.base_addr + 9w) 0w
                              (set_byte (s.base_addr + 8w) h'' uninitb' s.be) s.be);
          s.base_addr ↦
            Word
              (set_byte (s.base_addr + 7w) (w2w (w2w c : word32))
                 (set_byte (s.base_addr + 6w) (w2w (w2w h : word32))
                    (set_byte (s.base_addr + 5w) h'
                       (set_byte (s.base_addr + 4w) h
                          (set_byte (s.base_addr + 3w) 1w
                             (set_byte (s.base_addr + 1w) c uninitb s.be)
                             s.be) s.be) s.be) s.be) s.be)
        ⦈)’ >-
   (qunabbrev_tac ‘test’ >> qunabbrev_tac ‘st4’ >> qunabbrev_tac ‘st3’ >>
    qunabbrev_tac ‘st2’ >> qunabbrev_tac ‘st’ >>
    fs[mem_store_byte_def, write_bytearray_def, combinTheory.UPDATE_APPLY]) >>
  qunabbrev_tac ‘test’ >> rw[] >>
  PURE_REWRITE_TAC[ONE] >>
  rw[read_bytearray_1, mem_load_byte_def] >>
  (* almost there *)
  rw[Once future_safe_cases] >> disj1_tac >>
  rw[mux_backslash_pred_def] >-
   (cheat) >>
  (* show return 0 *)
  rw[h_prog_def, h_prog_rule_return_def,
     panLangTheory.size_of_shape_def, shape_of_def] >>
  rw[Once future_safe_cases]
QED

(*
Globals.max_print_depth := 30
*)




































(*/ loops!
   TODO an infinite example
 *)

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
