(*
 * actual pancake programs. simps used here.
 * properties needed for verification
 * - describing trees given arbitrary restrictions on ffi responses
 * - spec must be transparently related to the (correct) result of itree_evaluate
 * - skipping 'irrelevant' (e.g. logging) calls, optional
 *)

open panPtreeConversionTheory; (* parse_funs_to_ast *)
open panSemTheory; (* eval_def, byte stuff *)
open panLangTheory; (* size_of_shape_def *)
open arithmeticTheory;

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

Theorem itree_wbisim_refl[simp] = itree_wbisim_refl;
Theorem apply_update_simp[simp] = cj 1 combinTheory.UPDATE_APPLY;
(* may explode cases if k1 = k2 isn't decidable: luckily we cmp names = strings *)
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

Theorem word_add_neq:
  k ≠ 0w ∧ w2n (k : α word) < dimword (:α) ⇒ a + k ≠ a
Proof
  rw[]
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

val skip_tau = rw[Once future_safe_cases] >> disj2_tac;

(* needs to be α for type vars to match *)
Theorem future_safe_ignore_tau[simp]:
  (∀(t' : α sem32tree). ¬P (Tau t')) ⇒ (future_safe P (Tau t) ⇔ future_safe P t)
Proof
  rw[] >> rw[Once future_safe_cases]
QED

(*/ real
   XXX there's a semantic error caused by loading from drv_dequeue_c, read-only
   simp[ExclSF “LET”]
   Proof[exclude_frags = LET] ...

   DEP_REWRITE_TAC
 *)

val muxrx_ast = parse_pancake ‘
fun fn() {
  var drv_dequeue_c = @base;
  var drv_dequeue_a = @base + 1;
  #drv_dequeue_used(drv_dequeue_c, 1, drv_dequeue_a, 1);
// error, should not be written
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
// note: this is exactly the same as the first branch
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
  ((∃k.
     t = Vis (FFI_call "set_escape_character" [0w : word8] []) k ∧
     (* immediate return *)
     k (FFI_return ARB []) ≈ Ret (SOME (Return (ValWord 0w))))
   ∨ (t = Ret (SOME (Return (ValWord 0w))))
   ∨ ∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem mux_backslash_pred_notau:
  ¬mux_backslash_pred (Tau (t : α sem32tree))
Proof
  rw[mux_backslash_pred_def]
QED

Definition mux_set_escape_pred_def:
  mux_set_escape_pred (escape : word8) t =
  ((∃k. t = Vis (FFI_call "set_escape_character" [escape] []) k ∧
        k (FFI_return ARB []) ≈ Ret (SOME (Return (ValWord 0w))))
   ∨ ∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem mux_set_escape_pred_notau:
  ¬mux_set_escape_pred e (Tau (t : α sem32tree))
Proof
  rw[mux_set_escape_pred_def]
QED

Definition mux_at_pred_def:
  mux_at_pred (gchar : word32) t =
  (((gchar - 48w = 0w) ⇒ mux_set_escape_pred 0w t) ∧
   (1w ≤ gchar - 48w ⇒
    ∃k uninit.
     t = Vis (FFI_call "get_num_clients" [] [uninit]) k ∧
     ∀n.
     future_safe
     (λcont. ∃k2. (gchar - 48w) ≤ w2w n ⇒
                  cont = Vis (FFI_call "set_client" [w2w (gchar - 48w)] []) k2 ∧
                  future_safe (mux_set_escape_pred 0w) (k2 (FFI_return ARB [])))
     (k (FFI_return ARB [n])))
   ∨ ∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem word_moment:
  a < x ⇒ (1w + a) ≤ x
Proof
  cheat
QED

Theorem mux_at_pred_notau:
  (0w ≤ gchar - 48w) ⇒ ¬(mux_at_pred gchar) (Tau (t : α sem32tree))
Proof
  Cases_on ‘0w = gchar - 48w’ >> gvs[mux_at_pred_def, mux_set_escape_pred_def] >>
  strip_tac >>
  ‘0w < (gchar + 0xFFFFFFD0w) ∨ 0w = (gchar + 0xFFFFFFD0w)’
    by metis_tac[wordsTheory.WORD_LESS_OR_EQ] >-
   (pop_last_assum kall_tac >> pop_last_assum kall_tac >>
    ‘1w + 0w ≤ gchar + 0xFFFFFFD0w’ suffices_by rw[] >>
    rw[word_moment]) >-
   metis_tac[]
QED

Definition mux_escape_pred_def:
  mux_escape_pred (gchar : word32) t =
  (((gchar = 92w) ⇒ mux_set_escape_pred 1w t) ∧
   ((gchar = 64w) ⇒ mux_set_escape_pred 2w t) ∧
   ((gchar ≠ 92w ∧ gchar ≠ 64w) ⇒ future_safe mux_backslash_pred t))
End

Definition muxrx_pred_def:
  muxrx_pred t =
  ∀c.
  (∃k1 k2 uninit1 uninit2 uninit.
    (t = Vis (FFI_call "drv_dequeue_used" [uninit1] [uninit2]) k1) ∧
    (k1 (FFI_return ARB [c]) ≈
        Vis (FFI_call "get_escape_character" [] [uninit]) k2) ∧
    (* backslash escape case, transitions to zero *)
    future_safe mux_backslash_pred (k2 (FFI_return ARB [1w])) ∧
    (0w ≤ (w2w c : word32) - 48w
     ⇒ future_safe (mux_at_pred (w2w c)) (k2 (FFI_return ARB [2w]))) ∧
    future_safe (mux_escape_pred (w2w c)) (k2 (FFI_return ARB [0w]))
  ) ∨
  (∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem muxrx_pred_notau:
  ¬muxrx_pred (Tau (t : α sem32tree))
Proof
  rw[muxrx_pred_def]
QED

(* the proof *)

Theorem mux_return_branch_gen:
  ∀a0.
  future_safe mux_backslash_pred a0
  ⇒
  ∀branch f. a0 = (to_ffi branch : (α sem32tree))
             ⇒ future_safe mux_backslash_pred
                           (to_ffi
                            (bind branch (λ(res,s'). if res = NONE
                                                     then (f res s')
                                                     else Ret (res,s'))))
Proof
  ho_match_mp_tac future_safe_ind >>
  rw[] >-
   (fs[mux_backslash_pred_def] >-
     (rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_backslash_pred_def] >> disj1_tac >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[to_ffi_seq]) >-
     (rw[Once future_safe_cases] >> disj1_tac >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[mux_backslash_pred_def]) >-
     (rw[Once future_safe_cases] >> disj1_tac >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[mux_backslash_pred_def])) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Theorem branch_iter_pull_if:
  (λx. iter (mrec_cb h_prog)
            ((λ(res,s'). if res = NONE then (Vis (INL (p,s')) Ret)
                         else Ret (res,s')) x))
  = (λ(res,s').
        if res = NONE then
          (bind
           (mrec_cb h_prog (Vis (INL (p,s')) Ret))
           (λx. case x of INL a => Tau (iter (mrec_cb h_prog) a) | INR b => Ret b))
          else Ret (res,s'))
Proof
  rw[FUN_EQ_THM] >>
  Cases_on ‘x’ >> simp[Once itree_iter_thm] >>
  rw[itree_bind_thm]
QED

Triviality mux_return_branch:
 future_safe mux_backslash_pred (to_ffi branch : (α sem32tree))
 ⇒ future_safe mux_backslash_pred
               (to_ffi
                (bind branch (λ(res,s'). if res = NONE
                                         then (f res s')
                                         else Ret (res,s'))))
Proof
  metis_tac[mux_return_branch_gen]
QED

Triviality mux_return_branch_at:
 future_safe (mux_at_pred e) (to_ffi branch : (α sem32tree))
 ⇒ future_safe (mux_at_pred e)
               (to_ffi
                (bind branch (λ(res,s'). if res = NONE
                                         then (f res s')
                                         else Ret (res,s'))))
Proof
  cheat
QED

Triviality mux_return_branch_esc:
 future_safe (mux_escape_pred e) (to_ffi branch : (α sem32tree))
 ⇒ future_safe (mux_escape_pred e)
               (to_ffi
                (bind branch (λ(res,s'). if res = NONE
                                         then (f res s')
                                         else Ret (res,s'))))
Proof
  cheat
QED

(* TODO reuse proof for repeated program fragment *)

Definition the_word:
  the_word (Word v) = v
End

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
  ‘good_dimindex (:32)’ by EVAL_TAC >>
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
  rw[itree_wbisim_refl] >-
   (* backslash *)
   (qunabbrev_tac ‘k2’ >> qunabbrev_tac ‘rest’ >>
    assume_tac (GEN_ALL mux_backslash_pred_notau) >>
    rw[] >>
    ‘∃k. (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
         (byte_align (s.base_addr + 3w)) = Word k’
      by rw[write_bytearray_preserve_words] >>
    qmatch_goalsub_abbrev_tac ‘itree_mrec _ (_,st)’ >>
    subgoal ‘eval st (LoadByte (Var «escape_character_a»)) = SOME (ValWord 1w)’ >-
     (rw[eval_def, Abbr ‘st’] >> rw[load_write_bytearray_thm2]) >>
    drule dec_lifted >> rw[] >> pop_assum kall_tac >> pop_assum kall_tac >>
    rw[Once seq_thm] >>
    (* if the first bind (if-branch) returns we're done *)
    ho_match_mp_tac mux_return_branch >>

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
    (* is_word (mem addr) ⇒ is_word ((write_bytearray mem) addr) *)
   (*     fun2set in set_sepScript*)
    ‘∃k. (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
         (byte_align (s.base_addr + 4w)) = Word k’
      by rw[write_bytearray_preserve_words] >>
    subgoal ‘mem_load_byte st.memory st.memaddrs st.be (st.base_addr + 4w)
             = SOME uninitb'³'’ >-
     (qunabbrev_tac ‘st’ >> rw[load_write_bytearray_other]) >>
    (* vis *)
    rw[] >>
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
    (* check_num_to_chars *)
    rw[seq_thm] >>
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
    rw[read_bytearray_1] >>
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
     (rw[h_prog_def, h_prog_rule_return_def, size_of_shape_def, shape_of_def] >>
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
    (* XXX reproduce term literal error, reproduce matching fail from word tvars *)
    subgoal ‘mem_store_byte st3.memory st3.memaddrs st3.be
      (st3.base_addr + 6w) (w2w (w2w h : word32))
   = SOME (s.memory⦇
     s.base_addr ↦
     Word
     (set_byte (s.base_addr + 6w) (w2w (w2w h : word32))
               (set_byte (s.base_addr + 5w) h'
                         (set_byte (s.base_addr + 4w) h
                                   (set_byte (s.base_addr + 3w) 1w
                                             (set_byte (s.base_addr + 1w)
                                                       c uninitb
                                                     s.be) s.be) s.be) s.be) s.be)
            ⦈)’
    >-
    (* subgoal ‘mem_store_byte st3.memory st3.memaddrs st3.be *)
    (*  (st3.base_addr + 6w) (w2w (w2w h : word32)) *)
    (*  = SOME *)
    (*    st3.memory⦇ *)
    (*    st3.base_addr ↦ Word (set_byte (st3.base_addr + 6w) (w2w (w2w h : word32)) *)
    (*                                   (the_word (st3.memory st3.base_addr)) *)
    (*                                   st3.be)⦈’ >- *)
     (qunabbrev_tac ‘st3’ >> qunabbrev_tac ‘st2’ >> qunabbrev_tac ‘st’ >>
      fs[mem_store_byte_def, write_bytearray_def, the_word]) >>
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
     (PURE_REWRITE_TAC[TWO] >> PURE_REWRITE_TAC[ONE] >>
      qunabbrev_tac ‘st4’ >> qunabbrev_tac ‘st3’ >> qunabbrev_tac ‘st2’ >>
      qunabbrev_tac ‘st’ >>
      fs[miscTheory.read_bytearray_def, mem_load_byte_def,
         combinTheory.UPDATE_APPLY] >>
      rw[byteTheory.get_byte_set_byte, miscTheory.get_byte_set_byte_diff]) >>
    rw[] >>
    PURE_REWRITE_TAC[ONE] >>
    subgoal ‘st3.base_addr = s.base_addr ∧ st4.base_addr = s.base_addr ∧
             st4.memaddrs = s.memaddrs ∧ st4.be = s.be’ >-
     (qunabbrev_tac ‘st4’ >> qunabbrev_tac ‘st3’ >> qunabbrev_tac ‘st2’ >>
      qunabbrev_tac ‘st’ >> rw[]) >>
    ‘(byte_align (st3.base_addr + 8w)) = (byte_align (s.base_addr + 8w))’ by rw[] >>
    (* get memory map to compute *)
    ‘s.base_addr ≠ (s.base_addr + 8w)’ by rw[word_add_neq] >>
    ‘(s.base_addr + 8w) ∈ st4.memaddrs’ by rw[] >>
    rw[miscTheory.read_bytearray_def, mem_load_byte_def,
       combinTheory.UPDATE_APPLY] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[] >-
     (qunabbrev_tac ‘rest’ >> rw[Once future_safe_cases, mux_backslash_pred_def]) >>
    Cases_on ‘new_bytes’ >> fs[] >> pop_assum kall_tac >>
    qunabbrev_tac ‘rest’ >>
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
                                                       (set_byte (s.base_addr + 1w)
                                                                 c uninitb
                                                s.be) s.be) s.be) s.be) s.be) s.be)
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
                                                                  c uninitb
                                                 s.be) s.be) s.be) s.be) s.be) s.be)
        ⦈ (byte_align (st4.base_addr + 9w))’ >-
     (qunabbrev_tac ‘st4’ >> qunabbrev_tac ‘st3’ >> qunabbrev_tac ‘st2’ >>
      qunabbrev_tac ‘st’ >>
      fs[mem_store_byte_def, write_bytearray_def, combinTheory.UPDATE_APPLY]) >>
    rw[] >>
    qmatch_goalsub_abbrev_tac  ‘iter _ (_ test _ _)’ >>
    ‘(byte_align (st4.base_addr + 9w)) = (byte_align (s.base_addr + 9w))’ by rw[] >>
    subgoal
    ‘test =
     SOME (s.memory⦇
            s.base_addr + 8w ↦
              Word (set_byte (s.base_addr + 9w) 0w
                                              (set_byte (s.base_addr + 8w) h''
                                                        uninitb' s.be) s.be);
           s.base_addr ↦
             Word
            (set_byte (s.base_addr + 7w) (w2w (w2w c : word32))
                      (set_byte (s.base_addr + 6w) (w2w (w2w h : word32))
                                (set_byte (s.base_addr + 5w) h'
                                          (set_byte (s.base_addr + 4w) h
                                                    (set_byte (s.base_addr + 3w) 1w
                                                              (set_byte
                                                                (s.base_addr + 1w)
                                                                c uninitb
                                                 s.be) s.be) s.be) s.be) s.be) s.be)
        ⦈)’ >-
     (qunabbrev_tac ‘test’ >> qunabbrev_tac ‘st4’ >> qunabbrev_tac ‘st3’ >>
      qunabbrev_tac ‘st2’ >> qunabbrev_tac ‘st’ >>
      fs[mem_store_byte_def, write_bytearray_def, combinTheory.UPDATE_APPLY]) >>
    rw[] >>
    rw[h_prog_def, h_prog_rule_ext_call_def] >>
    PURE_REWRITE_TAC[ONE] >>
    rw[read_bytearray_1, mem_load_byte_def] >>
    (* almost there *)
    rw[Once future_safe_cases] >> disj1_tac >>
    rw[mux_backslash_pred_def] >-
     (rw[byteTheory.get_byte_set_byte]) >>
    (* show return 0 *)
    rw[h_prog_def, h_prog_rule_return_def, size_of_shape_def, shape_of_def] >>
   rw[itree_wbisim_refl])
  >-
   (* part 2 *)
   (qunabbrev_tac ‘k2’ >> qunabbrev_tac ‘rest’ >>
    assume_tac (GEN_ALL mux_at_pred_notau) >>
    rw[] >>
    ‘∃k. (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
         (byte_align (s.base_addr + 3w)) = Word k’
      by rw[write_bytearray_preserve_words] >>
    qmatch_goalsub_abbrev_tac ‘itree_mrec _ (_,st)’ >>
    subgoal ‘eval st (LoadByte (Var «escape_character_a»)) = SOME (ValWord 2w)’ >-
     (qunabbrev_tac ‘st’ >> rw[eval_def] >>
      rw[load_write_bytearray_thm2]) >>
    drule dec_lifted >> rw[] >> pop_assum kall_tac >> pop_assum kall_tac >>
    rw[Once seq_thm] >>
    rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
    (* not one *)
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[Once h_prog_def] >>
    rw[GSYM h_prog_def, GSYM itree_mrec_alt] >>
    rw[seq_thm] >>
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    (* junk *)
    ho_match_mp_tac mux_return_branch_at >>
    (* making escape_2 call... *)
    rw[GSYM itree_mrec_alt, seq_thm] >>
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[] >-
     (rw[Once future_safe_cases, mux_at_pred_def, mux_set_escape_pred_def]) >>
    subgoal ‘eval (st with
                      <|locals := st.locals |+ («escape_character»,ValWord 2w);
                                    memory := st.memory; ffi := new_ffi|>)
             (Op Sub [Var «got_char»; Const 48w]) =
                        (SOME (ValWord (w2w c + 0xFFFFFFD0w)))’ >-
     (qunabbrev_tac ‘st’ >> rw[eval_def, wordLangTheory.word_op_def]) >>
    drule dec_lifted >> rw[] >> pop_assum kall_tac >> pop_assum kall_tac >>
    rw[seq_thm] >>
    Cases_on ‘(w2w c + 0xFFFFFFD0w) < (1w : word32)’ >-
     (subgoal ‘byte_align (st.base_addr + 9w) ∈ st.memaddrs’ >-
       (qunabbrev_tac ‘st’ >> rw[]) >>
      rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[Once h_prog_def] >>
      rw[GSYM h_prog_def, GSYM itree_mrec_alt] >> (* baseaddr_ref *)
      rw[seq_thm] >>
      ‘∃k. (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
           (byte_align (s.base_addr + 8w)) = Word k’
        by rw[write_bytearray_preserve_words] >>
      ‘∃k. (write_bytearray (s.base_addr + 3w) [2w]
                 (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs
                    s.be) s.memaddrs s.be)
           (byte_align (s.base_addr + 8w)) = Word k’
        by rw[write_bytearray_preserve_words] >>
      rw[itree_mrec_alt, h_prog_def, h_prog_rule_store_byte_def] >>
      rw[mem_store_byte_def] >>
      subgoal ‘st.memory (byte_align (st.base_addr + 9w)) = Word k''’ >-
       (qunabbrev_tac ‘st’ >> rfs[]) >>
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
      rw[read_bytearray_1] >>
      rw[mem_load_byte_def] >>
      (* set_escape call *)
      rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_at_pred_def, mux_set_escape_pred_def] >-
       (rw[byteTheory.get_byte_set_byte]) >-
       (rw[h_prog_def, h_prog_rule_return_def, size_of_shape_def, shape_of_def]) >-
       (rw[wordsTheory.WORD_NOT_LESS_EQUAL])) >>
    rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[Once h_prog_def, h_prog_rule_dec_def] >>
    rw[Once eval_def, wordLangTheory.word_op_def] >>
    rw[Once h_prog_def, h_prog_rule_seq_def] >>
    rw[h_prog_def, h_prog_rule_ext_call_def] >>
    rw[read_bytearray_1] >>
    ‘∃w. write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be
                         (byte_align (s.base_addr + 4w)) = Word w’
      by rw[write_bytearray_preserve_words] >>
    subgoal ‘mem_load_byte st.memory st.memaddrs st.be (st.base_addr + 4w)
             = SOME uninitb'³'’ >-
     (qunabbrev_tac ‘st’ >> rw[] >>
      ‘∃w. write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be
                           (byte_align (s.base_addr + 3w)) = Word w’
        by rw[write_bytearray_preserve_words] >>
      rw[load_write_bytearray_other]) >>
    rw[] >>
    rw[Once future_safe_cases] >> disj1_tac >>
    rw[mux_at_pred_def, mux_set_escape_pred_def] >-
     (pop_assum kall_tac >> pop_assum kall_tac >>
      spose_not_then assume_tac >> fs[]) >>
    skip_tau >> skip_tau >>
    rw[h_prog_def, h_prog_rule_dec_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    subgoal ‘mem_load_byte
             (write_bytearray (st.base_addr + 4w) [n]
                              st.memory st.memaddrs st.be) st.memaddrs
             st.be (st.base_addr + 4w) = SOME n’ >-
     (qunabbrev_tac ‘st’ >> rw[] >>
      ‘∃w. (write_bytearray
            (s.base_addr + 3w) [2w]
            (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs
                             s.be) s.memaddrs s.be)
           (byte_align (s.base_addr + 4w)) = Word w’
        by rw[write_bytearray_preserve_words] >>
      rw[load_write_bytearray_thm2]) >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
    simp[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    Cases_on ‘(w2w n : word32) < w2w c + 0xFFFFFFD0w’ >-
     (rw[Once future_safe_cases] >> rw[wordsTheory.WORD_NOT_LESS_EQUAL]) >>
    rw[Once future_safe_cases] >> disj2_tac >>
    (* dec set_client_c *)
    rw[h_prog_def, h_prog_rule_dec_def] >>
    rw[Once eval_def, wordLangTheory.word_op_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[h_prog_def, h_prog_rule_seq_def] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[h_prog_rule_store_byte_def] >>
    subgoal ‘mem_store_byte
             (write_bytearray (st.base_addr + 4w) [n] st.memory
                              st.memaddrs st.be) st.memaddrs st.be
             (st.base_addr + 5w) (w2w (w2w c + 0xFFFFFFD0w : word32))
             = SOME (s.memory⦇
          s.base_addr ↦
            Word
              (set_byte (s.base_addr + 5w) (w2w (w2w c + 0xFFFFFFD0w : word32))
                 (set_byte (s.base_addr + 4w) n
                    (set_byte (s.base_addr + 3w) 2w
                       (set_byte (s.base_addr + 1w) c uninitb s.be) s.be)
                    s.be) s.be)
        ⦈)’ >-
     (qunabbrev_tac ‘st’ >> fs[mem_store_byte_def, write_bytearray_def]) >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[h_prog_def, h_prog_rule_ext_call_def] >>
    rw[read_bytearray_1] >>
    rw[mem_load_byte_def] >>
    subgoal ‘(byte_align (st.base_addr + 5w)) = s.base_addr’ >-
     (qunabbrev_tac ‘st’ >> rw[]) >>
    subgoal ‘s.base_addr ∈ st.memaddrs’ >- (qunabbrev_tac ‘st’ >> rw[]) >>
    rw[Once future_safe_cases] >> disj1_tac >>
    qmatch_goalsub_abbrev_tac ‘_ ⇒ (_ ∧ (k2 = _)) ∧ _’ >>
    qexists_tac ‘k2’ >> rw[] >-
     (qunabbrev_tac ‘st’ >> rw[byteTheory.get_byte_set_byte]) >>
    qunabbrev_tac ‘k2’ >> rw[] >>
    assume_tac (GEN_ALL mux_set_escape_pred_notau) >>
    rw[Once eval_def, wordLangTheory.word_op_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[h_prog_def, h_prog_rule_seq_def] >>
    rw[itree_mrec_alt, h_prog_def, h_prog_rule_store_byte_def] >>
    rw[mem_store_byte_def] >>
    subgoal ‘(byte_align (st.base_addr + 9w)) = s.base_addr + 8w’ >-
     (qunabbrev_tac ‘st’ >> rfs[]) >>
    ‘s.base_addr ≠ (s.base_addr + 8w)’ by rw[word_add_neq] >>
    simp[cj 2 combinTheory.UPDATE_APPLY] >>
    subgoal ‘s.base_addr + 8w ∈ st.memaddrs’ >-
     (qunabbrev_tac ‘st’ >> rw[]) >>
    rw[h_prog_def, h_prog_rule_seq_def] >>
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
    rw[read_bytearray_1] >>
    rw[mem_load_byte_def] >>
    (* set_escape call *)
    rw[Once future_safe_cases] >> disj1_tac >>
    rw[mux_at_pred_def, mux_set_escape_pred_def] >-
     (rw[byteTheory.get_byte_set_byte]) >-
     (rw[h_prog_def, h_prog_rule_return_def, size_of_shape_def, shape_of_def]))
  >- (* escape control received *)
   (qunabbrev_tac ‘k2’ >> qunabbrev_tac ‘rest’ >>
    rw[] >>
    ‘∃k. (write_bytearray (s.base_addr + 1w) [c] s.memory s.memaddrs s.be)
         (byte_align (s.base_addr + 3w)) = Word k’
      by rw[write_bytearray_preserve_words] >>
    qmatch_goalsub_abbrev_tac ‘itree_mrec _ (_,st)’ >>
    subgoal ‘eval st (LoadByte (Var «escape_character_a»)) = SOME (ValWord 0w)’ >-
     (qunabbrev_tac ‘st’ >> rw[eval_def] >> rw[load_write_bytearray_thm2]) >>
    drule dec_lifted >> rw[] >> pop_assum kall_tac >> pop_assum kall_tac >>
    rw[Once seq_thm] >>
    rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
    (* not one *)
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[h_prog_def, h_prog_rule_seq_def] >>
    rw[h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[h_prog_def, h_prog_rule_seq_def] >>
    rw[h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (rw[Once future_safe_cases] >> disj2_tac) >>
    (* making escape_0 call... *)
    rw[itree_mrec_bind] >>
    rw[branch_iter_pull_if] >>
    ho_match_mp_tac mux_return_branch_esc >>

    rw[GSYM itree_mrec_alt, seq_thm] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[] >-
     (rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >>
      simp[mux_escape_pred_def, mux_set_escape_pred_def] >>
      rw[Once future_safe_cases, mux_backslash_pred_def]) >>
    (* case split *)
    Cases_on ‘c = 92w’ >-
     (rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
      subgoal ‘FLOOKUP st.locals «got_char» = SOME (ValWord 92w)’ >-
       (qunabbrev_tac ‘st’ >> rw[]) >>
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      (* escape_case call *)
      rw[GSYM itree_mrec_alt, seq_thm] >>
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[] >-
       (rw[Once future_safe_cases] >> disj2_tac >>
        rw[Once future_safe_cases, mux_escape_pred_def, mux_set_escape_pred_def]) >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      ho_match_mp_tac mux_return_branch_esc >>
      (* exit after branch *)
      rw[baseaddr_ref] >> rw[seq_thm] >>
      subgoal ‘st.base_addr = s.base_addr’ >- (qunabbrev_tac ‘st’ >> rw[]) >>
      (* store byte *)
      rw[itree_mrec_alt, h_prog_def, h_prog_rule_store_byte_def] >>
      rw[mem_store_byte_def] >>
      ‘∃w. write_bytearray (s.base_addr + 3w) [0w]
           (write_bytearray (s.base_addr + 1w) [92w] s.memory s.memaddrs s.be)
           s.memaddrs s.be (byte_align (s.base_addr + 8w)) = Word w’
           by rw[write_bytearray_preserve_words] >>
      subgoal ‘st.memory (s.base_addr + 8w) = Word w’ >-
       (qunabbrev_tac ‘st’ >> rfs[]) >>
      subgoal ‘st.memaddrs = s.memaddrs’ >- (qunabbrev_tac ‘st’ >> rw[]) >>
      rw[h_prog_def, h_prog_rule_ext_call_def] >>
      rw[read_bytearray_1] >>
      rw[mem_load_byte_def] >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_escape_pred_def, mux_set_escape_pred_def] >-
       (rw[byteTheory.get_byte_set_byte]) >>
      rw[h_prog_def, h_prog_rule_return_def, size_of_shape_def, shape_of_def]) >>
    Cases_on ‘c = 64w’ >-
     (rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
      subgoal ‘FLOOKUP st.locals «got_char» = SOME (ValWord 64w)’ >-
       (qunabbrev_tac ‘st’ >> rw[]) >>
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[h_prog_def] >>
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      (* escape_case call *)
      rw[GSYM itree_mrec_alt, seq_thm] >>
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[] >-
       (rw[Once future_safe_cases] >> disj2_tac >>
        rw[Once future_safe_cases, mux_escape_pred_def, mux_set_escape_pred_def]) >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      ho_match_mp_tac mux_return_branch_esc >>
      rw[baseaddr_ref] >> rw[seq_thm] >>
      subgoal ‘st.base_addr = s.base_addr’ >- (qunabbrev_tac ‘st’ >> rw[]) >>
      (* store byte *)
      rw[itree_mrec_alt, h_prog_def, h_prog_rule_store_byte_def] >>
      rw[mem_store_byte_def] >>
      ‘∃w. write_bytearray (s.base_addr + 3w) [0w]
           (write_bytearray (s.base_addr + 1w) [64w] s.memory s.memaddrs s.be)
           s.memaddrs s.be (byte_align (s.base_addr + 8w)) = Word w’
           by rw[write_bytearray_preserve_words] >>
      subgoal ‘st.memory (s.base_addr + 8w) = Word w’ >-
       (qunabbrev_tac ‘st’ >> rfs[]) >>
      subgoal ‘st.memaddrs = s.memaddrs’ >- (qunabbrev_tac ‘st’ >> rw[]) >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[h_prog_def, h_prog_rule_ext_call_def] >>
      rw[read_bytearray_1] >>
      rw[mem_load_byte_def] >>
      rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_escape_pred_def, mux_set_escape_pred_def] >-
       (rw[byteTheory.get_byte_set_byte]) >>
      rw[h_prog_def, h_prog_rule_return_def, size_of_shape_def, shape_of_def]) >>
    (* normal *)
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
    subgoal ‘FLOOKUP st.locals «got_char» = SOME (ValWord (w2w c))’ >-
     (qunabbrev_tac ‘st’ >> rw[]) >>
    subgoal ‘(w2w c) ≠ (92w : word32)’ >-
     (qspecl_then [‘c’,‘92w’] strip_assume_tac (cj 1 addressTheory.w2w_CLAUSES) >>
      fs[]) >>
    subgoal ‘(w2w c) ≠ (64w : word32)’ >-
     (qspecl_then [‘c’,‘64w’] strip_assume_tac (cj 1 addressTheory.w2w_CLAUSES) >>
      fs[]) >>
    skip_tau >> skip_tau >> skip_tau >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[h_prog_def] >>
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[h_prog_def] >>
    skip_tau >> skip_tau >> skip_tau >> skip_tau >> skip_tau >> skip_tau >>
    pop_assum kall_tac >> pop_assum kall_tac >>
   )
QED

Theorem test:
  (a : α word) ≠ (b : α word) ∧
  dimword (:α) < dimword (:β) ⇒ (w2w a : β word) ≠ (w2w b : β word)
Proof
  rw[addressTheory.w2w_CLAUSES] >>

QED

(*
Globals.max_print_depth := 20
*)



































(*
 - properties can be stated in terms of (mrec_cb h_prog (p,s))
    P(i,s) ⇒ P(i',(mrec_cb h_prog (p,s)).s)

 Vis (INL p,s - execute) (λ(p,s) - cleanup-form),
 loop invariant: assert that h_prog_while's itree_iter produces:
 Vis (p,s)
   (λ(res, s'). Tau (
      Vis (p', s')  - satisfying pred on p', ⋆ (Ret INL) (λx. case INL -> iter...
        (λ ...)
   - using new state, execute loop condition again, then body
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

(* TODO fix *)
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
