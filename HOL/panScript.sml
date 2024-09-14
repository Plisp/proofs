(*
 * actual pancake programs. simps used here.
 * properties needed for verification
 * - describing trees given arbitrary restrictions on ffi responses
 * - spec must be transparently related to the (correct) result of itree_evaluate

 Globals.max_print_depth := 100
 Cond_rewr.stack_limit := 8
 *)

open preamble;
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
    rhs $ concl $ SRULE[] $ EVALn 1500 “(parse_funs_to_ast ^code)”
end

fun parse_pancake_nosimp q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “(parse_funs_to_ast ^code)”
end

val muxrx_ast = parse_pancake ‘
fun net_enqueue_free(1 queue_handle, 2 buffer) {
    var test = < 1 , 2 >;
    return test.0;
}
’;

(* XXX add_user_printer docs, sml-mode *)
(* fun omitprinter _ _ sys ppfns gs d t = *)
(* let open term_pp_utils term_pp_types smpp *)
(*   val (f , args) = strip_comb t *)
(*   val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs *)
(* in *)
(*   block PP.INCONSISTENT 0 *)
(*         (add_string "While" >> add_break(1,0) >> *)
(*          sys {gravs=gs,depth= decdepth d,binderp=false} (hd args) >> *)
(*                                          add_string " …") *)
(* end *)

(* val _ = temp_add_user_printer("omitprinter", “While _ x : 32 prog”, omitprinter); *)

(* XXX data structure (internal) correctness
   need correctness condition to be 'local' to some memory, write-invariant
   do this by proving 2 theorems:
   push (stack bounds (hol data) state) = stack newdata (same state)
   read_bytearray (outside bounds) (stack bounds (state)) = read_bytearray state
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

val assign_tac = gvs[Once itree_mrec_def, Once h_prog_def,
                     h_prog_rule_assign_def, eval_def];
val strb_tac = rw[Once itree_mrec_def, Once h_prog_def, h_prog_rule_store_byte_def];
Globals.max_print_depth := 25;

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

Theorem word_add_neq:
  k ≠ 0w ∧ w2n (k : α word) < dimword (:α) ⇒ a + k ≠ a
Proof
  rw[]
QED

(* TODO 64? *)
Definition mem_has_word_def:
  mem_has_word mem addr = ∃w. mem (byte_align addr) = Word (w : word32)
End

(* wfrites, disjoint_writes
  wordf ≡ disjointness, has Words

  prevent proliferation of write_bytearray (via disjointness)
  reads of disjoint_writes should compute if within a single region
  writes within boundaries (not necessarily current) preserve wf

  making new regions requires quadratic obligations for disjointness
 *)

Type write[pp] = “:(num # word8 list)”;
Type range[pp] = “:(num # num)”;
Definition range_disjoint_def:
  range_disjoint ((s1,l1) : range) ((s2,l2) : range)
  = ((s1 + l1 < s2) ∨ (s2 + l2 < s1))
End

Definition writes_disjoint_def:
  write_disjoint ((s1,l1) : write) ((s2,l2) : write)
  = range_disjoint (s1, LENGTH l1) (s2, LENGTH l2)
End

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

Theorem test:
  (w + 1 < dimword(:32)) ⇒
  n2w w <₊ n2w (w + 1) : word32
Proof
  rw[wordsTheory.word_lo_n2w]
QED

Theorem disjoint_write_byte:
  (∀a. a ∈ s.memaddrs) ∧
  (∀a. a < n2w (q + LENGTH r) ⇒ mem_has_word s.memory a) ∧
  (q + (LENGTH r) < dimword (:32))
  ∧
  range_disjoint (start, len) (q, LENGTH r) ∧
  start ≤ pos ∧ pos < len + start
  ⇒
  mem_load_byte
  (write_bytearray (n2w q) r s.memory s.memaddrs s.be)
  s.memaddrs s.be (n2w pos)
  = mem_load_byte s.memory s.memaddrs s.be (n2w pos)
Proof
  rw[range_disjoint_def] >-
   (‘pos < q’ by rw[] >>
    qpat_x_assum ‘pos < _ + _’ kall_tac >>
    qpat_x_assum ‘_ ≤ _’ kall_tac >>
    qpat_x_assum ‘_ + _ < _’ kall_tac >>
    pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
    qid_spec_tac ‘q’ >>
    Induct_on ‘r’ >>
    rw[write_bytearray_def] >>
    rw[mem_store_byte_def] >>
    subgoal ‘mem_has_word s.memory (n2w q)’ >-
     (first_x_assum match_mp_tac >>
      EVAL_TAC >>
      cheat
     ) >>
    ‘mem_has_word
     (write_bytearray (n2w q + 1w) r s.memory s.memaddrs s.be)
     (n2w q)’ by rw[write_bytearray_preserve_words] >>
    fs[mem_has_word_def] >>
    simp[mem_load_byte_def, SimpL “$=”] >>
    ‘n2w q + 1w = n2w (q + 1) : word32’
      by metis_tac[arithmeticTheory.SUC_ONE_ADD, arithmeticTheory.ADD_COMM,
                   wordsTheory.n2w_SUC] >>
    ‘n2w (LENGTH r) + n2w (q + 1) = n2w q + n2w (SUC (LENGTH r)) : word32’
      by metis_tac[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_COMM,
                   wordsTheory.n2w_SUC] >>
    last_x_assum $ qspec_then ‘q + 1’ strip_assume_tac >>
    gvs[arithmeticTheory.SUC_ONE_ADD] >>
    Cases_on ‘byte_align (n2w q) ≠ byte_align (n2w pos) : word32’ >-
     (gvs[combinTheory.UPDATE_APPLY, mem_load_byte_def]) >>
    ‘good_dimindex (:32)’ by EVAL_TAC >>
    gvs[miscTheory.get_byte_set_byte_diff, mem_load_byte_def]) >-
   (cheat
   )
QED

Inductive wordf:
  (wordf []) ∧
  (EVERY (write_disjoint a) as ∧ wordf as ⇒ wordf (a::as))
End

Theorem wordf_test:
  wordf [(3,[x]);(1,[c])]
Proof
  rw[Once wordf_cases] >-
   (rw[writes_disjoint_def, range_disjoint_def]) >>
  rw[Once wordf_cases] >>
  rw[Once wordf_cases]
QED

Definition bwrites_def:
  bwrites ([] : write list) s = s.memory ∧
  bwrites ((a,l)::as) s
  = write_bytearray (n2w a) l (bwrites as s) s.memaddrs s.be
End

Theorem bwrites_test:
  (write_bytearray (3w : word32) [x]
                   (write_bytearray 1w [c] s.memory s.memaddrs s.be)
                   s.memaddrs s.be)
  =
  bwrites [(3,[x]);(1,[c])] s
Proof
  rw[bwrites_def]
QED

Definition find_range:
  find_range (off,len) writes
  = FIND (λ(start : num, l : word8 list).
            start ≤ off ∧ off + len ≤ start + (LENGTH l)) writes
End

Theorem find_test:
  ∃v. find_range (1,1) [(3,[x]);(1,[c])] = SOME v
Proof
  rw[find_range, FIND_thm]
QED

Definition range_at:
  range_at (start,len) pos (b : word8) s
  = (start ≤ pos ∧ (pos < start + len) ∧
     mem_load_byte s.memory s.memaddrs s.be (n2w pos : word32) = SOME b)
End

Definition ranged_pred:
  ranged_pred P st start len =
  (∀q l.
     (∀a. a < n2w (q + LENGTH l) ⇒ mem_has_word st.memory a) ∧
     (q + LENGTH l) < dimword (:32) ∧
     P st ∧ range_disjoint (start, len) (q, LENGTH l)
     ⇒ P (st with memory := (bwrites [(q,l)] st)))
End

Theorem at_ranged:
  (∀a. a ∈ st.memaddrs) ⇒
  ranged_pred (range_at (start, len) pos b) st start len
Proof
  rw[ranged_pred, range_at, bwrites_def] >>
  irule EQ_TRANS >>
  first_x_assum $ irule_at Any >>
  match_mp_tac disjoint_write_byte >>
  gvs[]
QED

Theorem conj_ranged:
  ranged_pred P st start len ∧ ranged_pred Q st start len
  ⇒ ranged_pred (λst. P st ∧ Q st) st start len
Proof
  rw[ranged_pred]
QED

Theorem disj_ranged:
  (ranged_pred P st start len ∧ ranged_pred Q st start len)
  ⇒ ranged_pred (λst. P st ∨ Q st) st start len
Proof
  rw[ranged_pred] >> metis_tac[]
QED

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

(* PURE_ONCE_REWRITE_TAC[ *)
(*       prove(“(iter (muxtx_body s (w2n h)) 0) = *)
(*              (iter (muxtx_body s (w2n h)) (w2n (0w : word32)))”, rw[])] >> *)
(* Globals.max_print_depth := 200; *)

(* Theorem test: *)
(*   client < w2n h ⇒ *)
(*   trim_itree tx_ev_pred *)
(*   (bind (iter (muxtx_body s (w2n h)) client) cleanup) = ARB *)
(* Proof *)
(*   simp[Once itree_iter_thm, muxtx_body] >> *)
(*   simp[Once itree_iter_thm, muxtx_cli_loop] >> *)
(* QED *)

(* write a tactic?
goal = (term list, term)
tactic = goal -> goal list * validation

foo_tac = fn goal => (tactic) goal
*)

(*/
   loops!
 *)

val while_ast = parse_pancake ‘
fun fn() {
  var base = @base;
  #getc(0, 0, @base, 1);

  var i = 0;
  while (42 == 42) {
    if (i == 0) {
      #ffi(0, 0, 0, 0);
      i = 1;
    } else {
      #test(0, 0, 0, 0);
      if (ldb base) == 0 {
        return;
      }
      strb base, (ldb base) - 1;
      i = 0;
    }
  }
}’;

Definition while_sem_def:
  while_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD ^while_ast) s
End
