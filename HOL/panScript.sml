(*
 * actual pancake programs. simps used here.
 * properties needed for verification
 * - describing trees given arbitrary restrictions on ffi responses
 * - spec must be transparently related to the (correct) result of itree_evaluate

 Globals.max_print_depth := 15
 Cond_rewr.stack_limit := 8
 *)

open panPtreeConversionTheory; (* parse_funs_to_ast *)
open panSemTheory; (* eval_def, byte stuff *)
open panLangTheory; (* size_of_shape_def *)
open arithmeticTheory;
open listTheory;

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

fun parse_pancake_nosimp q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “(parse_funs_to_ast ^code)”
end

(* fun omitprinter _ _ sys _ gs d = *)
(*   sys {gravs=gs,depth=2,binderp=false} o fst o dest_comb; *)
(* val _ = temp_add_user_printer ("omitprinter", “OMIT x : 32 prog”, omitprinter); *)

(* TODO ring buffer (internal) correctness
   need correctness condition to be 'local' to some memory, write-invariant
 *)

(* Theorem test: *)
(*   s.code = (FEMPTY |+ («f», ([(«n», One)], (Return (Var «n»))))) ⇒ *)
(*   itree_evaluate (Dec «r» (Const 0w) (Call NONE (Label «f») [Var «r»])) s *)
(*   = ARB *)
(* Proof *)
(*   rw[itree_evaluate_alt] >> *)
(*   rw[itree_mrec_alt, h_prog_def, h_prog_rule_dec_def] >> *)
(*   rw[eval_def] >> *)
(*   rw[h_prog_def] >> *)
(*   rw[h_prog_rule_call_def] >> *)
(*   rw[eval_def] >> *)
(*   rw[finite_mapTheory.FLOOKUP_UPDATE] >> *)
(*   rw[lookup_code_def, shape_of_def] >> *)
(*   rw[finite_mapTheory.FLOOKUP_UPDATE] >> *)
(* QED *)





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

Theorem seq_simp[simp] = seq_thm;
Theorem valid_value_simp[simp] = is_valid_value_def;
Theorem shape_of_simp[simp] = shape_of_def;
Theorem h_prog_skip[simp] = cj 1 h_prog_def;

val assign_tac = gvs[Once itree_mrec_alt, Once h_prog_def,
                     h_prog_rule_assign_def, eval_def];
val strb_tac = rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_store_byte_def];

(*/ word nonsense
   inst type vars: INST_TYPE [gamma |-> beta, alpha |-> beta, beta |-> gamma]
   word_add_n2w
 *)

Theorem align_offset:
  aligned (LOG2 (dimindex (:32) DIV 8)) (addr : word32) ∧
  w2n n < (dimindex (:32) DIV 8)
  ⇒ byte_align (addr + n) = addr
Proof
  rw[alignmentTheory.byte_align_def] >>
  rw[alignmentTheory.align_add_aligned]
QED

val align_thm = LIST_CONJ [alignmentTheory.byte_aligned_def,
                           alignmentTheory.byte_align_def,
                           alignmentTheory.aligned_def,
                           align_offset];

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

Definition mem_has_word_def:
  mem_has_word mem addr = ∃w. mem (byte_align addr) = Word (w : word32)
End

(* wfrites, disjoint_writes
  wordf ≡ disjointness, has Words

  TODO: prevent proliferation of write_bytearray (via disjointness)
  reads of disjoint_writes should compute if within a single region
  writes within boundaries (not necessarily current) preserve wf

  making new regions requires quadratic obligations for disjointness

  maybe look into fun2set in set_sepScript
 *)

(* Definition writes_disjoint_def: *)
(*   write_disjoint (s1,l1) (s2,l2) *)
(*   = ((s1 + n2w(LENGTH l1) < s2) ∨ (s2 + n2w(LENGTH l2) < s1)) *)
(* End *)

(* Inductive wordf: *)
(*   (wordf []) ∧ *)
(*   (EVERY (write_disjoint a) as ∧ wordf as ⇒ wordf (a::as)) *)
(* End *)

(* Definition bwrites_def: *)
(*   bwrites [] s = s.memory ∧ *)
(*   bwrites ((off,l)::as) s *)
(*   = write_bytearray (s.base_addr + off) l (bwrites as s) s.memaddrs s.be *)
(* End *)

(* Theorem join_bwrites: *)
(*   write_bytearray (s.base_addr + off) bs (bwrites [] s) s.memaddrs s.be *)
(* Proof *)
(* QED *)

(* Theorem test: *)
(*   (write_bytearray *)
(*   (s.base_addr + (3w : word32)) [x] *)
(*   (write_bytearray (s.base_addr + 1w) [c] s.memory *)
(*                    s.memaddrs s.be) s.memaddrs s.be) *)
(*   = *)
(*   bwrites [(3w : word32,[x]);(1w : word32,[c])] s *)
(* Proof *)
(*   rw[bwrites_def] *)
(* QED *)

(* Theorem test2: *)
(*   wordf [(3w : word32,[x]);(1w : word32,[c])] *)
(* Proof *)
(*   rw[Once wordf_cases] >- *)
(*    (rw[writes_disjoint_def]) >> *)
(*   rw[Once wordf_cases] >> *)
(*   rw[Once wordf_cases] *)
(* QED *)

(*
  old byte theorems
 *)

Theorem store_bytearray_1:
  byte_align addr ∈ dm ∧ mem_has_word m addr ⇒
  mem_store_byte m dm be addr b =
  SOME (write_bytearray addr [b] m dm be)
Proof
  rw[write_bytearray_def, mem_store_byte_def] >>
  Cases_on ‘m (byte_align addr)’ >> gvs[] >>
  fs[mem_has_word_def]
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

(* spose_not_then kall_tac *)
Theorem load_write_bytearray_thm2:
  (∀(w : word32). w ∈ s.memaddrs) ⇒
  mem_load_byte (write_bytearray addr [v] oldmem s.memaddrs s.be)
                s.memaddrs s.be addr
  = if (mem_has_word oldmem addr) then (SOME v) else NONE
Proof
  rw[mem_has_word_def] >-
   (rw[mem_load_byte_def, write_bytearray_def] >>
    rw[mem_store_byte_def] >>
    rw[byteTheory.get_byte_set_byte]) >>
  Cases_on ‘oldmem (byte_align addr)’ >> fs[] >>
  rw[mem_load_byte_def, write_bytearray_def] >>
  rw[mem_store_byte_def]
QED

Definition the_word[simp]:
  the_word (Word v) = v
End

Theorem load_write_bytearray_other:
  (∀(w : word32). w ∈ s.memaddrs) ∧
  other ≠ addr
  ⇒
  mem_load_byte (write_bytearray other [c] smem s.memaddrs s.be)
                s.memaddrs s.be addr
  =
  if (mem_has_word smem addr ∧ mem_has_word smem other)
  then mem_load_byte smem s.memaddrs s.be addr
  else if (mem_has_word smem addr)
  then SOME (get_byte addr (the_word (smem (byte_align addr))) s.be)
  else NONE
Proof
  rw[mem_has_word_def,
     mem_load_byte_def, write_bytearray_def, mem_store_byte_def] >-
   (Cases_on ‘byte_align addr = byte_align other’ >>
    rw[] >-
     (gvs[] >>
      irule miscTheory.get_byte_set_byte_diff >>
      rw[] >> EVAL_TAC) >>
    rw[combinTheory.UPDATE_APPLY]) >-
   (gvs[] >> Cases_on ‘smem (byte_align other)’ >> fs[]) >>
  Cases_on ‘smem (byte_align addr)’ >> gvs[] >>
  Cases_on ‘smem (byte_align other)’ >> gvs[] >>
  Cases_on ‘byte_align addr = byte_align other’ >> gvs[] >>
  rw[combinTheory.UPDATE_APPLY]
QED

Theorem write_bytearray_preserve_words:
  mem_has_word oldmem w ⇒
  mem_has_word (write_bytearray loc l oldmem s.memaddrs s.be) w
Proof
  simp[mem_has_word_def] >>
  strip_tac >>
  qid_spec_tac ‘loc’ >> Induct_on ‘l’ >>
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
  fs[eval_def, wordLangTheory.word_op_def, dec_lifted]
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
   XXX pancake multiple definitions? shape access checks .0.0.0.0?

fun enq({1} root, {1} e) {
    var head_a = root - 2;
    var tail_a = root - 1;
    var head = load head_a;
    var tail = load tail_a;

    store ((root + head) % 999), e;
    store head_a, (head + 1);
    return 0;
}

fun deq({1} root) {
    var head_a = root - 2;
    var tail_a = root - 1;
    var head = load head_a;
    var tail = load tail_a;

    ret = load ((root + tail) % 999);
    store tail_a, (tail + 1);
    return ret;
}

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

Definition mux_set_escape_pred_def:
  mux_set_escape_pred (escape : word8) t =
  ((∃k.
     t = Vis (FFI_call "set_escape_character" [escape] []) k ∧
     k (FFI_return ARB []) ≈ Ret (SOME (Return (ValWord 0w)))
   )
   ∨ ∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem mux_set_escape_pred_notau:
  ¬mux_set_escape_pred e (Tau (t : α sem32tree))
Proof
  rw[mux_set_escape_pred_def]
QED

Definition mux_checked_set_escape_pred_def:
  mux_checked_set_escape_pred (escape : word8) t =
  ((∃uninit k.
     t = Vis (FFI_call "check_num_to_get_chars" [] [uninit]) k ∧
     k (FFI_return ARB [0w]) ≈ Ret (SOME (Return (ValWord 0w))) ∧
     future_safe (mux_set_escape_pred 0w) (k (FFI_return ARB [1w]))
   )
   ∨ ∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem mux_checked_set_escape_pred_notau:
  ¬mux_checked_set_escape_pred e (Tau (t : α sem32tree))
Proof
  rw[mux_checked_set_escape_pred_def]
QED

Definition mux_at_pred_def:
  mux_at_pred (gchar : word32) t =
  ((gchar - 48w < 1w ⇒ mux_set_escape_pred 0w t) ∧
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

Theorem mux_at_pred_notau:
  ¬(mux_at_pred gchar) (Tau (t : α sem32tree))
Proof
  gvs[mux_at_pred_def, mux_set_escape_pred_def] >>
  rw[wordsTheory.WORD_LESS_OR_EQ] >>
  blastLib.BBLAST_TAC
QED

Definition mux_escape_pred_def:
  mux_escape_pred (gchar : word32) t =
  (((gchar = 92w) ⇒ mux_set_escape_pred 1w t) ∧
   ((gchar = 64w) ⇒ mux_set_escape_pred 2w t) ∧
   ((gchar ≠ 92w ∧ gchar ≠ 64w) ⇒ (mux_checked_set_escape_pred 0w) t))
End

Theorem mux_escape_pred_notau:
  ¬mux_escape_pred e (Tau (t : α sem32tree))
Proof
  rw[mux_escape_pred_def,mux_set_escape_pred_def,mux_checked_set_escape_pred_def] >>
  blastLib.BBLAST_TAC
QED

Definition muxrx_pred_def:
  muxrx_pred t =
  ∀c.
  (∃k1 k2 uninit1 uninit2 uninit.
    (t = Vis (FFI_call "drv_dequeue_used" [uninit1] [uninit2]) k1) ∧
    (k1 (FFI_return ARB [c]) ≈
        Vis (FFI_call "get_escape_character" [] [uninit]) k2) ∧
    (* backslash escape case, transitions to zero *)
    future_safe (mux_checked_set_escape_pred 0w) (k2 (FFI_return ARB [1w])) ∧
    future_safe (mux_at_pred (w2w c)) (k2 (FFI_return ARB [2w])) ∧
    future_safe (mux_escape_pred (w2w c)) (k2 (FFI_return ARB [0w]))
  ) ∨
  (∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem muxrx_pred_notau:
  ¬muxrx_pred (Tau (t : α sem32tree))
Proof
  rw[muxrx_pred_def]
QED

(*
 the proof
*)

Triviality mux_uncond_set_branch:
  ∀branch.
  future_safe (mux_set_escape_pred e) (to_ffi branch : (α sem32tree))
  ⇒ future_safe (mux_set_escape_pred e)
                (to_ffi
                 (bind branch (λ(res,s'). if res = NONE
                                          then (f res s')
                                          else Ret (res,s'))))
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (fs[mux_set_escape_pred_def] >-
     (rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_set_escape_pred_def] >> disj1_tac >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[to_ffi_seq]) >-
     (rw[Once future_safe_cases] >> disj1_tac >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[mux_set_escape_pred_def])) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Triviality mux_set_client_branch:
  ∀t.
  future_safe (λcont. ∃k2.
                e + 0xFFFFFFD0w ≤ w2w n ⇒
                cont =
                Vis (FFI_call "set_client" [w2w (e + 0xFFFFFFD0w)] []) k2 ∧
                future_safe (mux_set_escape_pred 0w) (k2 (FFI_return ARB [])))
  (to_ffi t : (α sem32tree)) ⇒
  future_safe (λcont. ∃k2.
                e + 0xFFFFFFD0w ≤ w2w n ⇒
                cont =
                Vis (FFI_call "set_client" [w2w (e + 0xFFFFFFD0w)] []) k2 ∧
                future_safe (mux_set_escape_pred 0w) (k2 (FFI_return ARB [])))
              (to_ffi (bind t (λ(res,s'). if res = NONE
                                          then (f res s')
                                          else Ret (res,s'))))
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (rw[Once future_safe_cases] >> disj1_tac >>
    Cases_on ‘e + 0xFFFFFFD0w ≤ w2w n’ >>
    gvs[GSYM wordsTheory.WORD_NOT_LESS_EQUAL] >>
    gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[mux_uncond_set_branch]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Triviality set_escape_seq:
  mux_checked_set_escape_pred e (to_ffi t) ⇒
  mux_checked_set_escape_pred
  e
  (to_ffi
   (bind t
         (λ(res,s'). if res = NONE then f NONE s' else Ret (res,s'))))
Proof
  gvs[mux_checked_set_escape_pred_def] >> rw[] >-
   (disj1_tac >>
    gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs(),
        Once itree_wbisim_cases] >>
    qmatch_goalsub_abbrev_tac ‘bind t _’ >>
    qmatch_goalsub_abbrev_tac ‘future_safe _ (to_ffi (bind t1 _))’ >>
    cheat
   ) >-
   (disj2_tac >>
    gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()])
QED

Triviality mux_checked_set_branch:
  ∀t.
  future_safe (mux_checked_set_escape_pred e) (to_ffi t) ⇒
  future_safe (mux_checked_set_escape_pred e)
  (to_ffi
   (bind t
         (λ(res,s'). if res = NONE then f NONE s' else Ret (res,s'))))
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (rw[Once future_safe_cases] >> disj1_tac >> rw[set_escape_seq]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Triviality mux_return_branch_at:
 ∀branch.
 future_safe (mux_at_pred e) (to_ffi branch : (α sem32tree))
 ⇒ future_safe (mux_at_pred e)
               (to_ffi
                (bind branch (λ(res,s'). if res = NONE
                                         then (f res s')
                                         else Ret (res,s'))))
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (rw[Once future_safe_cases] >> disj1_tac >>
    fs[mux_at_pred_def] >>
    Cases_on ‘e + 0xFFFFFFD0w < 1w’ >> gvs[GSYM wordsTheory.WORD_NOT_LESS_EQUAL] >-
     (fs[mux_set_escape_pred_def] >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[to_ffi_seq]) >-
     (gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      strip_tac >> pop_last_assum $ qspec_then ‘n’ assume_tac >>
      rw[mux_set_client_branch]) >-
     (gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()]) >-
     (gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()])) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Triviality mux_return_branch_esc:
 ∀branch.
 future_safe (mux_escape_pred e) (to_ffi branch : (α sem32tree))
 ⇒ future_safe (mux_escape_pred e)
               (to_ffi
                (bind branch (λ(res,s'). if res = NONE
                                         then (f res s')
                                         else Ret (res,s'))))
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (rw[Once future_safe_cases] >> disj1_tac >>
    rw[mux_escape_pred_def] >> fs[mux_escape_pred_def] >-
     (fs[mux_set_escape_pred_def] >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[to_ffi_seq]) >-
     (fs[mux_set_escape_pred_def] >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[to_ffi_seq]) >-
     (fs[set_escape_seq])) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Theorem escape_pred_to_backslash:
  ∀t. future_safe (mux_checked_set_escape_pred 0w) (t : α sem32tree)
      ⇒ (w2w c) ≠ (92w : word32) ∧ (w2w c) ≠ (64w : word32)
      ⇒ future_safe (mux_escape_pred (w2w c)) t
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (rw[Once future_safe_cases] >> disj1_tac >>
    rw[mux_escape_pred_def]) >-
   (rw[Once future_safe_cases] >> disj2_tac >>
    pop_last_assum irule >>
    gvs[Once future_safe_cases] >>
    fs[mux_checked_set_escape_pred_notau]) >>
  rw[Once future_safe_cases]
QED

(*
  proof TODO fix alignment assumption
 *)

Definition muxrx_mem_assms:
  muxrx_mem s =
  ((∀(w : word32). w ∈ (s : (32,α) state).memaddrs) ∧
  (byte_align s.base_addr = s.base_addr) ∧
  (byte_align (s.base_addr + 1w) = s.base_addr) ∧
  (byte_align (s.base_addr + 3w) = s.base_addr) ∧
  (byte_align (s.base_addr + 4w) = s.base_addr) ∧
  (byte_align (s.base_addr + 5w) = s.base_addr) ∧
  (byte_align (s.base_addr + 6w) = s.base_addr) ∧
  (byte_align (s.base_addr + 7w) = s.base_addr) ∧
  (byte_align (s.base_addr + 8w) = (s.base_addr + 8w)) ∧
  (byte_align (s.base_addr + 9w) = (s.base_addr + 8w)) ∧
  mem_has_word s.memory s.base_addr ∧
  mem_has_word s.memory (s.base_addr + 8w))
End

Theorem escape_set_branch:
  muxrx_mem (s : (32, α) state)
  ⇒
  future_safe
  (mux_checked_set_escape_pred 0w : α sem32tree -> bool)
  (to_ffi
   (bind
    (itree_mrec h_prog
                (ExtCall «get_client» (Const 0w) (Const 0w)
                         (Var «client_a») (Const 1w),
                 s with
                   <|locals :=
                     s.locals |+ («drv_dequeue_c»,ValWord s.base_addr) |+
                      («drv_dequeue_a»,ValWord (s.base_addr + 1w)) |+
                      («got_char»,ValWord (w2w c)) |+
                      («escape_character_a»,ValWord (s.base_addr + 3w)) |+
                      («escape_character»,ValWord (w2w x)) |+
                      («client_a»,ValWord (s.base_addr + 4w));
                     memory :=
                     write_bytearray
                     (s.base_addr + 3w) [x]
                     (write_bytearray (s.base_addr + 1w) [c] s.memory
                                      s.memaddrs s.be) s.memaddrs s.be;
                     ffi := new_ffi|>))
    (λ(res,s').
       if res = NONE then
         Tau
         (itree_mrec
          h_prog
          (Dec «client» (LoadByte (Var «client_a»))
               (Dec «check_num_to_get_chars_a»
                    (Op Add [BaseAddr; Const 5w])
                    (Seq
                     (ExtCall «check_num_to_get_chars» (Const 0w)
                              (Const 0w) (Var «check_num_to_get_chars_a»)
                              (Const 1w))
                     (Dec «num_to_get_chars_ret»
                          (LoadByte (Var «check_num_to_get_chars_a»))
                          (Seq
                           (If
                            (Cmp Equal (Var «num_to_get_chars_ret»)
                                 (Const 0w)) (Return (Const 0w)) Skip)
                           (Dec «cli_dequeue_enqueue_c»
                                (Op Add [BaseAddr; Const 6w])
                                (Dec «cli_dequeue_enqueue_a»
                                     (Op Add [BaseAddr; Const 8w])
                                     (Seq
                                      (StoreByte
                                       (Var «cli_dequeue_enqueue_c»)
                                       (Var «client»))
                                      (Seq
                                       (StoreByte
                                        (Op Add
                                            [Var
                                             «cli_dequeue_enqueue_c»;
                                             Const 1w])
                                        (Var «got_char»))
                                       (Seq
                                        (ExtCall
                                         «batch_cli_dequeue_enqueue»
                                         (Var
                                          «cli_dequeue_enqueue_c»)
                                         (Const 2w)
                                         (Var
                                          «cli_dequeue_enqueue_a»)
                                         (Const 1w))
                                        (Dec
                                         «set_escape_character_c»
                                         (Op Add
                                             [BaseAddr; Const 9w])
                                         (Seq
                                          (StoreByte
                                           (Var
                                            «set_escape_character_c»)
                                           (Const 0w))
                                          (Seq
                                           (ExtCall
                                            «set_escape_character»
                                            (Var
                                             «set_escape_character_c»)
                                            (Const 1w)
                                            (Const 0w)
                                            (Const 0w))
                                           (Return (Const 0w)))))))))))))),s'))
       else Ret (res, s'))))
Proof
  ‘good_dimindex (:32)’ by EVAL_TAC >>
  assume_tac (GEN_ALL mux_checked_set_escape_pred_notau) >>
  assume_tac (GEN_ALL muxrx_pred_notau) >>
  rw[muxrx_mem_assms] >>
  gvs[mem_has_word_def] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  rw[read_bytearray_1] >>
  simp[write_bytearray_preserve_words, mem_has_word_def,
       load_write_bytearray_other] >>
  rw[mem_load_byte_def] >>
  (* vis *)
  rw[Once future_safe_cases] >> disj2_tac >>
  rw[] >-
   (rw[Once future_safe_cases, mux_checked_set_escape_pred_def]) >>
  Cases_on ‘new_bytes’ >> fs[] >> pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac ‘Seq (ExtCall _ _ _ _ _) rest’ >>
  fs[Once dec_lifted, eval_def, mem_has_word_def,
     write_bytearray_preserve_words, load_write_bytearray_thm2] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  rw[read_bytearray_1] >>
  fs[mem_has_word_def, write_bytearray_preserve_words,
     load_write_bytearray_other] >>
  rw[mem_load_byte_def] >>
  (* ffi check_num_to_get_chars, h' return *)
  rw[Once future_safe_cases] >> disj1_tac >>
  rw[mux_checked_set_escape_pred_def] >-
   (rw[Abbr ‘rest’] >>
    fs[Once dec_lifted, eval_def, mem_has_word_def,
       write_bytearray_preserve_words, load_write_bytearray_thm2] >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[h_prog_def, h_prog_rule_return_def, size_of_shape_def]) >>
  assume_tac (GEN_ALL mux_set_escape_pred_notau) >>
  rw[Abbr ‘rest’] >>
  qmatch_goalsub_abbrev_tac ‘Seq (ExtCall _ _ _ _ _) rest’ >>
  fs[Once dec_lifted, eval_def, mem_has_word_def,
     write_bytearray_preserve_words, load_write_bytearray_thm2] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
  rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  strb_tac >>
  qmatch_goalsub_abbrev_tac ‘(iter _ (_ (mem_store_byte thing _ _ _ _) _ _))’ >>
  subgoal ‘mem_has_word thing (s.base_addr + 6w)’ >-
   (qunabbrev_tac ‘thing’ >>
    gvs[mem_has_word_def, write_bytearray_preserve_words]) >>
  rw[store_bytearray_1] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_store_byte_def,
     eval_def, wordLangTheory.word_op_def] >>
  gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  PURE_REWRITE_TAC[TWO] >> rw[miscTheory.read_bytearray_def] >>
  rw[load_write_bytearray_other, load_write_bytearray_thm2,
     mem_has_word_def, write_bytearray_preserve_words] >>
  PURE_REWRITE_TAC[ONE] >> rw[read_bytearray_1] >>
  rw[load_write_bytearray_thm2, mem_has_word_def, write_bytearray_preserve_words] >>
  qmatch_goalsub_abbrev_tac ‘(_ (mem_load_byte mem2 _ _ _) _ _)’ >>
  subgoal ‘mem_has_word mem2 (s.base_addr + 8w)’ >-
   (rw[Abbr ‘thing’, Abbr ‘mem2’] >>
    ‘mem_has_word s.memory (s.base_addr + 8w)’ by rw[mem_has_word_def] >>
    irule write_bytearray_preserve_words >>
    irule write_bytearray_preserve_words >> (* Cond_rewr.stack_limit = 6 *)
    gvs[write_bytearray_preserve_words]) >>
  fs[mem_has_word_def, mem_load_byte_def] >>
  rw[Once future_safe_cases] >> disj2_tac >>
  qunabbrev_tac ‘rest’ >> rw[] >-
   (rw[Once future_safe_cases, mux_set_escape_pred_def]) >>
  Cases_on ‘new_bytes’ >> fs[] >> pop_assum kall_tac >>
  strb_tac >>
  gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  PURE_REWRITE_TAC[ONE] >>
  rw[read_bytearray_1] >>
  qmatch_goalsub_abbrev_tac
  ‘option_CASE (mem_load_byte (write_bytearray _ _ oldmem _ _) _ _ _) _ _’ >>
  subgoal ‘mem_has_word oldmem (s.base_addr + 9w)’ >-
   (gvs[Abbr ‘oldmem’, Abbr ‘thing’, mem_has_word_def,
        write_bytearray_preserve_words]) >>
  gvs[load_write_bytearray_thm2] >>
  (* almost there *)
  rw[Once future_safe_cases] >> disj1_tac >>
  rw[mux_set_escape_pred_def] >>
  (* show return 0 *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_return_def, size_of_shape_def]
QED

Theorem muxrx_correct:
  muxrx_mem s ⇒ future_safe muxrx_pred (muxrx_sem s)
Proof
  ‘good_dimindex (:32)’ by EVAL_TAC >>
  rw[muxrx_mem_assms, muxrx_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  assume_tac (GEN_ALL muxrx_pred_notau) >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  rfs[read_bytearray_1, mem_has_word_def, mem_load_byte_def] >>
  rw[Once future_safe_cases] >> disj1_tac >> rw[muxrx_pred_def] >>
  fs[dec_lifted, eval_def, mem_has_word_def, load_write_bytearray_thm2] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  simp[read_bytearray_1, load_write_bytearray_other, mem_load_byte_def,
       mem_has_word_def] >>
  qpat_abbrev_tac ‘b3 = get_byte _ _ _’ >> qmatch_goalsub_abbrev_tac ‘Vis _ k2’ >>
  qexistsl_tac [‘k2’, ‘b3’] >>
  qunabbrev_tac ‘k2’ >> rw[itree_wbisim_refl] >-
   (* backslash *)
   (assume_tac (GEN_ALL mux_checked_set_escape_pred_notau) >> rw[] >>
    gvs[dec_lifted, eval_def, write_bytearray_preserve_words, mem_has_word_def,
       load_write_bytearray_thm2] >>
    (* if the first bind (if-branch) returns we're done, discard rest *)
    ho_match_mp_tac mux_checked_set_branch >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def] >>
    rw[GSYM itree_mrec_alt, seq_thm] >>
    (* escape_1 *)
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[] >-
     (rw[Once future_safe_cases, mux_checked_set_escape_pred_def]) >>
    PURE_REWRITE_TAC[
        prove(“ValWord (1w : word32) = ValWord (w2w (1w : word8))”, rw[])] >>
    irule escape_set_branch >>
    gvs[muxrx_mem_assms, mem_has_word_def])
  >- (* part 2 *)
   (assume_tac (GEN_ALL mux_at_pred_notau) >> rw[] >>
    qmatch_goalsub_abbrev_tac ‘Seq (ExtCall _ _ _ _ _) rest’ >>
    fs[Once dec_lifted, eval_def, mem_has_word_def,
       write_bytearray_preserve_words, load_write_bytearray_thm2] >>
    (* not 1 *)
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[Once h_prog_def] >>
    (* not 2 *)
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def,
       Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[GSYM itree_mrec_alt, seq_thm] >>
    ho_match_mp_tac mux_return_branch_at >> rw[Abbr ‘rest’] >>
    (* making escape_2 call... *)
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[] >-
     (rw[Once future_safe_cases, mux_at_pred_def, mux_set_escape_pred_def]) >>
    rw[dec_lifted, eval_def, wordLangTheory.word_op_def] >>

    reverse
    (rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def,
        Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE]) >-
     (strb_tac >>
      gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
      gvs[read_bytearray_1, write_bytearray_preserve_words,
          load_write_bytearray_thm2, mem_has_word_def] >>
      rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_at_pred_def] >-
       (rw[mux_set_escape_pred_def] >>
        rw[Once itree_mrec_alt, h_prog_def,
           h_prog_rule_return_def, size_of_shape_def]) >>
      Cases_on ‘¬(w2w c + 0xFFFFFFD0w < (1w : word32))’ >> gvs[] >>
      rw[wordsTheory.WORD_NOT_LESS_EQUAL]) >>
    rw[h_prog_def, h_prog_rule_dec_def, eval_def, wordLangTheory.word_op_def] >>
    rw[h_prog_rule_seq_def] >>
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
    gvs[read_bytearray_1, write_bytearray_preserve_words,
        load_write_bytearray_other, mem_has_word_def] >>
    rw[mem_load_byte_def] >>
    rw[Once future_safe_cases] >> disj1_tac >>
    simp[mux_at_pred_def] >>
    subgoal ‘¬(w2w c + 0xFFFFFFD0w < (1w : word32)) ∧
             (1w : word32) ≤ w2w c + 0xFFFFFFD0w’ >-
     (Cases_on ‘¬(w2w c + 0xFFFFFFD0w < (1w : word32))’ >> gvs[] >>
      metis_tac[wordsTheory.WORD_NOT_LESS_EQUAL]) >>
    rw[] >> skip_tau >> skip_tau >>
    rw[Once h_prog_def, h_prog_rule_dec_def, eval_def] >>
    gvs[read_bytearray_1, write_bytearray_preserve_words,
        load_write_bytearray_thm2, mem_has_word_def] >>
    skip_tau >>
    rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
    reverse(
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE]) >-
     (skip_tau >>
      rw[Once future_safe_cases] >> disj1_tac >>
      subgoal ‘¬(w2w c + (0xFFFFFFD0w : word32) ≤ w2w n)’ >-
       (Cases_on ‘¬(w2w n < (w2w c) + (0xFFFFFFD0w : word32))’ >>
        gvs[wordsTheory.WORD_NOT_LESS_EQUAL]) >>
      rw[]) >>
    rw[] >> skip_tau >>
    rw[Once h_prog_def, h_prog_rule_dec_def,
       eval_def, wordLangTheory.word_op_def] >> skip_tau >>
    rw[Once h_prog_def, h_prog_rule_seq_def] >> skip_tau >>
    rw[Once h_prog_def, h_prog_rule_store_byte_def] >>
    gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
    rw[Once h_prog_def, h_prog_rule_store_byte_def] >>
    gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
    skip_tau >> rw[Once h_prog_def, h_prog_rule_ext_call_def] >>
    gvs[read_bytearray_1, write_bytearray_preserve_words,
        load_write_bytearray_thm2, mem_has_word_def] >>
    rw[Once future_safe_cases] >> disj1_tac >>
    qmatch_goalsub_abbrev_tac ‘_ ⇒ k2 = _ ∧ _’ >>
    qexists_tac ‘k2’ >> rw[] >>
    qunabbrev_tac ‘k2’ >> rw[] >> skip_tau >> skip_tau >> skip_tau >>
    rw[h_prog_def, h_prog_rule_seq_def] >> skip_tau >>
    rw[h_prog_rule_store_byte_def] >>
    qmatch_goalsub_abbrev_tac ‘(_ (mem_store_byte mem2 _ _ _ _) _ _)’ >>
    subgoal ‘mem_has_word mem2 (s.base_addr + 9w)’ >-
     (rw[Abbr ‘mem2’] >>
      ‘mem_has_word s.memory (s.base_addr + 9w)’ by rw[mem_has_word_def] >>
      gvs[write_bytearray_preserve_words]) >>
    gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
    skip_tau >>
    rw[h_prog_def, h_prog_rule_seq_def] >> skip_tau >>
    rw[h_prog_rule_ext_call_def] >>
    gvs[read_bytearray_1, write_bytearray_preserve_words,
        load_write_bytearray_thm2, mem_has_word_def] >>
    rw[Once future_safe_cases] >> disj1_tac >>
    rw[mux_set_escape_pred_def] >>
    rw[h_prog_def, h_prog_rule_return_def, size_of_shape_def])
  >- (* escape control received *)
   (assume_tac (GEN_ALL mux_escape_pred_notau) >> rw[] >>
    fs[Once dec_lifted, eval_def, mem_has_word_def,
       write_bytearray_preserve_words, load_write_bytearray_thm2] >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    (* not one *)
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[Once h_prog_def, h_prog_rule_seq_def] >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[Once h_prog_def, h_prog_rule_seq_def] >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    (* making escape_0 call... *)
    ho_match_mp_tac mux_return_branch_esc >>
    rw[GSYM itree_mrec_alt, seq_thm] >>
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[] >-
     (rw[Once future_safe_cases] >>
      simp[mux_escape_pred_def, mux_set_escape_pred_def] >>
      rw[Once future_safe_cases, mux_checked_set_escape_pred_def]) >>
    (* case split *)
    Cases_on ‘c = 92w’ >-
     (rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[GSYM itree_mrec_alt, seq_thm] >>
      (* escape_case call *)
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[] >-
       (rw[Once future_safe_cases, mux_escape_pred_def, mux_set_escape_pred_def]) >>
      ho_match_mp_tac mux_return_branch_esc >>
      (* exit after branch *)
      rw[baseaddr_ref] >>
      strb_tac >>
      gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
      gvs[read_bytearray_1, write_bytearray_preserve_words,
          load_write_bytearray_thm2, mem_has_word_def] >>
      rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_escape_pred_def, mux_set_escape_pred_def] >>
      rw[itree_mrec_alt, h_prog_def, h_prog_rule_return_def, size_of_shape_def]) >>
    Cases_on ‘c = 64w’ >-
     (rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      (* escape_case call *)
      rw[GSYM itree_mrec_alt, seq_thm] >>
      rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[] >-
       (rw[Once future_safe_cases, mux_escape_pred_def, mux_set_escape_pred_def]) >>
      ho_match_mp_tac mux_return_branch_esc >>
      rw[baseaddr_ref] >>
      strb_tac >>
      gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
      rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
      gvs[read_bytearray_1, write_bytearray_preserve_words,
          load_write_bytearray_thm2, mem_has_word_def] >>
      rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_escape_pred_def, mux_set_escape_pred_def] >>
      rw[Once itree_mrec_alt, Once h_prog_def,
         h_prog_rule_return_def, size_of_shape_def]) >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    simp[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    subgoal ‘(w2w c) ≠ (92w : word32)’ >-
     (qspecl_then [‘c’,‘92w’] strip_assume_tac (cj 1 addressTheory.w2w_CLAUSES) >>
      fs[]) >>
    subgoal ‘(w2w c) ≠ (64w : word32)’ >-
     (qspecl_then [‘c’,‘64w’] strip_assume_tac (cj 1 addressTheory.w2w_CLAUSES) >>
      fs[]) >>
    rw[Once h_prog_def, h_prog_rule_seq_def] >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    irule escape_pred_to_backslash >> rw[] >>
    PURE_REWRITE_TAC[
        prove(“ValWord (0w : word32) = ValWord (w2w (0w : word8))”, rw[])] >>
    irule escape_set_branch >>
    rw[muxrx_mem_assms, mem_has_word_def])
QED










(*
  muxtx
*)

val muxtx_ast = parse_pancake ‘
fun fn() {
var clients = 0;
var num_clients_a = @base;
// Get the number of clients as defined in our FFI file
#num_clients(0, 0, num_clients_a, 1);
clients = ldb num_clients_a;

// Check if the driver's tx used ring was empty.
var drv_was_empty_c = @base + 1;
var drv_was_empty_a = @base + 2;
// Store 0 as arg to get the used ring
strb drv_was_empty_c, 0;
#drv_ring_empty(drv_was_empty_c, 1, drv_was_empty_a, 1);
var was_empty = ldb drv_was_empty_a;

var client = 0;
while (client < clients) {
    // Loop through all of the current client's available ring
    var cli_dequeue_used_c = @base + 3;
    var cli_dequeue_used_a = @base + 4;

    strb cli_dequeue_used_c, client;
    #dequeue_used(cli_dequeue_used_c, 1, cli_dequeue_used_a, 24);
    var dequeue_used_ret = ldb cli_dequeue_used_c;

    while (dequeue_used_ret != 1) {
        // We now want to copy this buffer over to the drv shared ring buffers
        (* var drv_enqueue_dequeue_a = @base + 29; *)
        (* #batch_driver_dequeue_enqueue(cli_dequeue_used_a,24,drv_enqueue_dequeue_a,1); *)
        (* var driver_dequeue_enqueue_ret = ldb drv_enqueue_dequeue_a; *)
        (* if (driver_dequeue_enqueue_ret != 0) { *)
        (*     return 1; *)
        (* } *)

        var cli_enqueue_avail_a = @base + 30;
        strb cli_enqueue_avail_a, client;
        // Enqueue buffer back into the client available ring
        #cli_enqueue_avail(cli_dequeue_used_a, 24, cli_enqueue_avail_a, 1);

        // Continue to next iteration of the loop
        strb cli_dequeue_used_c, client;
        #dequeue_used(cli_dequeue_used_c, 1, cli_dequeue_used_a, 24);
        dequeue_used_ret = ldb cli_dequeue_used_c;
    }

    client = client + 1;
}

// If we were empty before, notify the driver that we have something to print
if (was_empty == 1) {
    #notify_driver(0,0,0,0);
}

return 0;
}’;

Definition muxtx_sem_def:
  muxtx_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD ^muxtx_ast) s
End

Definition trim_itree:
  trim_itree Pa t =
  itree_unfold (λt. case t of
                      Ret r => Ret' r
                    | Tau t => Tau' t
                    | Vis e k => Vis' e (λa. if (Pa e a) then (k a)
                                             else (Ret (SOME Error))))
               t
End

Theorem trim_itree_alt[simp]:
  trim_itree P (Ret r) = Ret r ∧
  trim_itree P (Tau t) = Tau (trim_itree P t) ∧
  trim_itree P (Vis e k) = Vis e (λa. if (P e a) then (trim_itree P (k a))
                                      else (Ret (SOME Error)))
Proof
  rw[trim_itree] >> rw[FUN_EQ_THM, Once itree_unfold] >>
  rw[FUN_EQ_THM] >>
  rw[Once itree_unfold]
QED

Definition tx_ev_pred[simp]:
  tx_ev_pred (FFI_call s conf buf) a =
  case a of
    (FFI_return s bs) => (LENGTH bs = LENGTH buf)
  | (FFI_final a) => F
End

Definition muxtx_mem_assms:
  muxtx_mem s =
  ((∀(w : word32). w ∈ (s : (32,α) state).memaddrs) ∧
   (∀n. n < 32 ⇒ mem_has_word s.memory (s.base_addr + n2w n)) ∧
   (byte_aligned s.base_addr))
End

(*
  muxtx proof
  since this follows a different protocol (reading from the read buffer)
  I will insert an assumption about that one byte changing
 *)

Definition muxtx_cli_loop:
  muxtx_cli_loop s client _ =
  (let w = (the_word (s.memory s.base_addr)) in
     let w' = (the_word (s.memory (s.base_addr + 4w))) in
       Vis (FFI_call "dequeue_used" [n2w client]
                     [get_byte (s.base_addr + 4w) w' s.be])
           (λ(res : α ffi_result).
              case res of
                (FFI_return _ [used]) =>
                  if used ≠ 1w
                  then (Vis (FFI_call "cli_enqueue_avail"
                                      [get_byte (s.base_addr + 4w) w' s.be]
                                      [n2w client])
                            (λres. Ret (INL ())))
                  else (Ret (INR (NONE : word32 result option)))))
End

Definition muxtx_body:
  muxtx_body s (n_clients : num) k =
  let w = (the_word (s.memory (s.base_addr + 4w))) in
    if k = n_clients then Ret (INR (NONE : word32 result option))
    else (bind (iter (muxtx_cli_loop s k) ())
               (λres. Ret (INL (k + 1))))
End

Definition muxtx_spec:
  muxtx_spec s =
  (let w = (the_word (s.memory s.base_addr)) in
   trim_itree tx_ev_pred
   (Vis (FFI_call "num_clients" [] [get_byte s.base_addr w s.be])
    (λres.
       case res of
         (FFI_return _ [n]) =>
           Vis (FFI_call "drv_ring_empty" [0w] [get_byte (s.base_addr + 2w) w s.be])
               (λres.
                  case res of
                    (FFI_return _ [b]) =>
                      bind (iter (muxtx_body s (w2n n)) 0)
                           (λres. if b = 1w
                                  then Vis (FFI_call "notify_driver" [] [])
                                           (λres. Ret (SOME (Return (ValWord 0w))))
                                  else (Ret (SOME (Return (ValWord 0w)))))
        ))))
End

Definition state1:
  state1 client rest f' h' h s =
  (trim_itree
   (tx_ev_pred :sem_vis_event -> α ffi_result -> bool)
   (to_ffi
    (bind
     (iter
      (mrec_cb (h_prog :32 prog # (32, α) state -> (32, α) mtree))
      (bind
       (h_prog
        (Seq
         (StoreByte (Var «cli_dequeue_used_c»)
                    (Var «client»))
         (Seq
          (ExtCall «dequeue_used»
                   (Var «cli_dequeue_used_c») (Const 1w)
                   (Var «cli_dequeue_used_a») (Const 24w))
          (Dec «dequeue_used_ret»
               (LoadByte (Var «cli_dequeue_used_c»))
               (Seq
                (While
                 (Cmp NotEqual
                      (Var «dequeue_used_ret»)
                      (Const 1w))
                 (Dec «cli_enqueue_avail_a»
                      (Op Add [BaseAddr; Const 30w])
                      (Seq
                       (StoreByte
                        (Var
                         «cli_enqueue_avail_a»)
                        (Var «client»))
                       (Seq
                        (ExtCall
                         «cli_enqueue_avail»
                         (Var
                          «cli_dequeue_used_a»)
                         (Const 24w)
                         (Var
                          «cli_enqueue_avail_a»)
                         (Const 1w))
                        (Seq
                         (StoreByte
                          (Var
                           «cli_dequeue_used_c»)
                          (Var «client»))
                         (Seq
                          (ExtCall
                           «dequeue_used»
                           (Var
                            «cli_dequeue_used_c»)
                           (Const 1w)
                           (Var
                            «cli_dequeue_used_a»)
                           (Const 24w))
                          (Assign
                           «dequeue_used_ret»
                           (LoadByte
                            (Var
                             «cli_dequeue_used_c»)))))))))
                (Assign «client»
                        (Op Add [Var «client»; Const 1w]))))),
         s with
           <|locals :=
             s.locals |+ («clients»,ValWord 0w) |+
              («num_clients_a»,ValWord s.base_addr) |+
              («clients»,ValWord (w2w h)) |+
              («drv_was_empty_c»,
                ValWord (s.base_addr + 1w)) |+
              («drv_was_empty_a»,
                ValWord (s.base_addr + 2w)) |+
              («was_empty»,ValWord (w2w h')) |+
              («client»,ValWord (n2w client)) |+
              («cli_dequeue_used_c»,
                ValWord (s.base_addr + 3w)) |+
              («cli_dequeue_used_a»,
                ValWord (s.base_addr + 4w));
             memory :=
             write_bytearray (s.base_addr + 2w) [h']
                             (write_bytearray (s.base_addr + 1w) [0w]
                                              (write_bytearray s.base_addr [h]
                                                               s.memory s.memaddrs s.be)
                                              s.memaddrs s.be) s.memaddrs s.be;
             ffi := f'|>))
       (λ(x :32 result option # (32, α) state).
          bind
          (revert_binding
           «cli_dequeue_used_a»
           (s with
              <|locals :=
                s.locals |+
                 («clients»,ValWord 0w) |+
                 («num_clients_a»,
                   ValWord s.base_addr) |+
                 («clients»,ValWord (w2w h)) |+
                 («drv_was_empty_c»,
                   ValWord (s.base_addr + 1w)) |+
                 («drv_was_empty_a»,
                   ValWord (s.base_addr + 2w)) |+
                 («was_empty»,ValWord (w2w h')) |+
                 («client»,ValWord (n2w client)) |+
                 («cli_dequeue_used_c»,
                   ValWord (s.base_addr + 3w));
                memory :=
                write_bytearray (s.base_addr + 2w)
                                [h']
                                (write_bytearray
                                 (s.base_addr + 1w) [0w]
                                 (write_bytearray s.base_addr
                                                  [h] s.memory s.memaddrs
                                                  s.be) s.memaddrs s.be)
                                s.memaddrs s.be; ffi := f'|>) x)
          (λx.
             bind
             (revert_binding «cli_dequeue_used_c»
                             (s with
                                <|locals :=
                                  s.locals |+
                                   («clients»,ValWord 0w) |+
                                   («num_clients_a»,
                                     ValWord s.base_addr) |+
                                   («clients»,ValWord (w2w h)) |+
                                   («drv_was_empty_c»,
                                     ValWord (s.base_addr + 1w)) |+
                                   («drv_was_empty_a»,
                                     ValWord (s.base_addr + 2w)) |+
                                   («was_empty»,
                                     ValWord (w2w h')) |+
                                   («client»,
                                     ValWord (n2w client));
                                  memory :=
                                  write_bytearray
                                  (s.base_addr + 2w) [h']
                                  (write_bytearray
                                   (s.base_addr + 1w) [0w]
                                   (write_bytearray
                                    s.base_addr [h]
                                    s.memory s.memaddrs
                                    s.be) s.memaddrs
                                   s.be) s.memaddrs s.be;
                                  ffi := f'|>) x)
             (λ(x :32 result option # (32, α) state).
                bind
                ((λ(res, s').
                    h_prog_whilebody_cb
                    (Dec
                     «cli_dequeue_used_c»
                     (Op Add
                         [BaseAddr;
                          Const 3w])
                     (Dec
                      «cli_dequeue_used_a»
                      (Op Add
                          [BaseAddr;
                           Const 4w])
                      (Seq
                       (StoreByte
                        (Var
                         «cli_dequeue_used_c»)
                        (Var
                         «client»))
                       (Seq
                        (ExtCall
                         «dequeue_used»
                         (Var
                          «cli_dequeue_used_c»)
                         (Const
                          1w)
                         (Var
                          «cli_dequeue_used_a»)
                         (Const
                          24w))
                        (Dec
                         «dequeue_used_ret»
                         (LoadByte
                          (Var
                           «cli_dequeue_used_c»))
                         (Seq
                          (While
                           (Cmp
                            NotEqual
                            (Var
                             «dequeue_used_ret»)
                            (Const
                             1w))
                           (Dec
                            «cli_enqueue_avail_a»
                            (Op
                             Add
                             [BaseAddr;
                              Const
                              30w])
                            (Seq
                             (StoreByte
                              (Var
                               «cli_enqueue_avail_a»)
                              (Var
                               «client»))
                             (Seq
                              (ExtCall
                               «cli_enqueue_avail»
                               (Var
                                «cli_dequeue_used_a»)
                               (Const
                                24w)
                               (Var
                                «cli_enqueue_avail_a»)
                               (Const
                                1w))
                              (Seq
                               (StoreByte
                                (Var
                                 «cli_dequeue_used_c»)
                                (Var
                                 «client»))
                               (Seq
                                (ExtCall
                                 «dequeue_used»
                                 (Var
                                  «cli_dequeue_used_c»)
                                 (Const
                                  1w)
                                 (Var
                                  «cli_dequeue_used_a»)
                                 (Const
                                  24w))
                                (Assign
                                 «dequeue_used_ret»
                                 (LoadByte
                                  (Var
                                   «cli_dequeue_used_c»)))))))))
                          (Assign «client» (Op Add [Var «client»; Const 1w]))))))))
                    res s' : (32 result option #
                                                        (32, α) state,
                                                        32 prog #
                                                        (32, α) state +
                                                        sem_vis_event #
                                                        (α ffi_result ->
                                                         32 result option #
                                                         (32, α) state),
                                                        32 prog #
                                                        (32, α) state +
                                                        32 result option #
                                                        (32, α) state) itree) x)
                (λx.
                   case x of
                     INL a =>
                       Tau
                       (iter
                        (λ(p',s').
                           h_prog_while_cb
                           (p',s')
                           (case FLOOKUP s'. locals «client»
                            of
                              SOME (ValWord w1) =>
                                (case FLOOKUP s'. locals «clients»
                                 of SOME (ValWord w2)
                                    => SOME (ValWord (if w1 < w2 then 1w else 0w))
                                 | _ => (NONE :32 v option))
                            | _ => NONE : 32 v option))
                        a)
                   | INR b => Ret b))))))
     (rest :32 result option # (32, α) state ->
                            (32 result option # (32, α) state,
                             sem_vis_event #
                             (α ffi_result ->
                              32 result option # (32, α) state),
                             32 result option # (32, α) state) itree))))
End

val vis_tac = irule itree_wbisim_vis >> Cases;

Theorem test:
  (muxtx_mem s) ⇒ trim_itree tx_ev_pred (muxtx_sem s) ≈ muxtx_spec s
Proof
  rw[muxtx_sem_def, muxtx_mem_assms, muxtx_spec, itree_evaluate_alt] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  rw[read_bytearray_1, mem_load_byte_def] >>
  subgoal ‘byte_align s.base_addr = s.base_addr ∧
           ∃w. s.memory s.base_addr = Word w’ >-
   (fs[align_thm] >>
    qpat_x_assum ‘∀n. n < 32 => _’ $ qspec_then ‘0’ assume_tac >>
    gvs[mem_has_word_def, alignmentTheory.byte_align_def]) >>
  rw[] >>
  vis_tac >> rw[] >> Cases_on ‘l’ >> fs[] >> pop_assum kall_tac >>
  assign_tac >>
  rfs[mem_has_word_def, load_write_bytearray_thm2] >>
  (* store byte *)
  subgoal ‘byte_align (s.base_addr + 1w) = s.base_addr’ >- fs[align_thm] >>
  strb_tac >>
  gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  gvs[read_bytearray_1, write_bytearray_preserve_words,
      load_write_bytearray_thm2, mem_has_word_def] >>
  subgoal ‘byte_align (s.base_addr + 2w) = s.base_addr’ >- fs[align_thm] >>
  subgoal ‘s.base_addr ≠ (s.base_addr + 2w)’ >- (rw[word_add_neq]) >>
  gvs[write_bytearray_preserve_words,load_write_bytearray_other,mem_has_word_def] >>
  rw[mem_load_byte_def] >>
  vis_tac >> rw[eval_def] >> Cases_on ‘l’ >>
  gvs[write_bytearray_preserve_words,load_write_bytearray_thm2,mem_has_word_def] >>
  qmatch_goalsub_abbrev_tac ‘bind _ rest’ >>
  PURE_ONCE_REWRITE_TAC[
      prove(“(iter (muxtx_body s (w2n h)) 0) =
             (iter (muxtx_body s (w2n h)) (w2n (0w : word32)))”, rw[])] >>
  qmatch_goalsub_abbrev_tac ‘While _ loop’ >>
  (* we want for each value of clients - client (0)
     - restrictions on state
     - dequeue_used and cli_enqueue_avail to correspond
   *)
  irule itree_wbisim_coind_upto >>
  qexists_tac
  ‘λprog spec.
     ∃client.
    client ≤ (w2n h)
    ∧
    prog = (state1 client rest f' h' h s)
    ∧
    spec =
    (trim_itree tx_ev_pred
                (bind (iter (muxtx_body s (w2n h)) client)
                      (λres.
                         if h' = 1w then
                           Vis (FFI_call "notify_driver" [] [])
                               (λres. Ret (SOME (Return (ValWord 0w))))
                         else Ret (SOME (Return (ValWord 0w))))))’ >>
  rpt strip_tac >-
   (disj2_tac >> qunabbrev_tac ‘loop’ >>
    fs[state1] >>
    cheat >>
    disj1_tac >>
    qmatch_goalsub_abbrev_tac ‘bind (iter _ _) cleanup’ >>
    simp[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_while_alt] >>
    simp[Once itree_iter_thm] >>
    simp[Once itree_iter_thm] >>
    ‘(n2w client : word32) < w2w h’ by cheat >>
    simp[eval_def, asmTheory.word_cmp_def] >>
    simp[Once h_prog_def, h_prog_rule_dec_alt] >>
    simp[eval_def, wordLangTheory.word_op_def] >>
    simp[Once h_prog_def, h_prog_rule_dec_alt] >>
    simp[eval_def, wordLangTheory.word_op_def] >>

    simp[Once h_prog_def, h_prog_rule_seq_def] >>
    rw[]
    cheat
   ) >>
   >> (* Globals.max_print_depth := 20 *)
  qexists_tac ‘0’ >> rw[]
QED

∃e k k'. strip_tau t (Vis e k) ∧ strip_tau t' (Vis e k') ∧  (∀r. R (k r) (k' r))
Theorem test:
  (trim_itree tx_ev_pred (iter (muxtx_body s (w2n h)) (w2n 0w))) = ARB
Proof
  simp[Once itree_iter_thm, muxtx_body] >>
  ‘h ≠ 0w’ by cheat >>
  simp[Once itree_iter_thm, muxtx_cli_loop] >>
QED

for equal case later
Cases_on ‘client = w2n h’ >-
   (or3_tac >>
    simp[Once itree_iter_thm, muxtx_body] >>
    simp[itree_mrec_alt, Once h_prog_def, h_prog_rule_while_alt] >>
    simp[Once itree_iter_thm] >>
    simp[Once itree_iter_thm] >>
    ‘n2w (w2n h) = (w2w h : word32)’ by cheat >>
    simp[eval_def, asmTheory.word_cmp_def] >>
    qunabbrev_tac ‘rest’ >>
    simp[itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    Cases_on ‘h' = 1w’ >-
     (simp[eval_def, asmTheory.word_cmp_def] >>
      rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
      vis_tac >> rw[] >> gvs[] >>
      rw[Once itree_mrec_alt, Once h_prog_def,
         h_prog_rule_return_def, size_of_shape_def, shape_of_def]) >>
    simp[eval_def, asmTheory.word_cmp_def] >>
    ‘w2w h' ≠ 1w : word32’ by cheat >> simp[] >>
    rw[Once itree_mrec_alt, Once h_prog_def,
       h_prog_rule_return_def, size_of_shape_def, shape_of_def])
   simp[]






























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

(*/
   loops!
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
  rw[dec_lifted]
  (* seq *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
  rw[read_bytearray_1, mem_load_byte_def] >>
  rw[Once future_safe_cases] >> disj1_tac >>
  rw[while_pred_def] >>
  rw[GSYM h_prog_rule_while_alt] >>
  Cases_on ‘n’ >>
  ‘w2n (n2w n' : word8) = n' - 0’ by rw[wordsTheory.w2n_n2w] >>
  drule (INST_TYPE [gamma |-> alpha] while_sem_lem) >> rw[] >>
  pop_assum $ qspecl_then [‘n'’, ‘0’] strip_assume_tac >>
  fs[wordsTheory.WORD_LT]
QED

(* write a tactic?
goal = (term list, term)
tactic = goal -> goal list * validation

foo_tac = fn goal => (tactic) goal
*)
