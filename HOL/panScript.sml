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
open set_sepTheory;

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
    rhs $ concl $ SRULE[] $ EVAL “(parse_funs_to_ast ^code)”
end

fun parse_pancake_nosimp q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “(parse_funs_to_ast ^code)”
end

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

(* need correctness condition to be 'local' to some memory, write-invariant
   do this by proving 2 theorems:
   push (stack bounds (hol data) state) = stack newdata (same state)
   read_bytearray (outside bounds) (stack bounds (state)) = read_bytearray state
 *)

Theorem pan_eval_simps[simp]:
    eval s (Const w) = SOME (ValWord w)
  ∧ eval s (Var v) = FLOOKUP s.locals v
  ∧ eval s BaseAddr = SOME (ValWord s.base_addr)
  ∧ eval s (Label fname) = OPTION_IGNORE_BIND (FLOOKUP s.code fname)
                                              (SOME (ValLabel fname))
  ∧ eval s (BytesInWord :32 exp) = SOME (ValWord 4w)
Proof
  rw[eval_def] >>
  Cases_on ‘FLOOKUP s.code fname’ >> rw[bytes_in_word_def]
QED

Theorem itree_wbisim_refl[simp] = itree_wbisim_refl;
Theorem apply_update_simp[simp] = cj 1 combinTheory.UPDATE_APPLY;
(* may explode cases if k1 = k2 isn't decidable: luckily we cmp names = strings *)
Theorem do_flookup_simp[simp] = finite_mapTheory.FLOOKUP_UPDATE;
Theorem valid_value_simp[simp] = is_valid_value_def;
Theorem shape_of_simp[simp] = shape_of_def;

(* TODO replace with setSep *)
Theorem read_bytearray_0[simp] = cj 1 miscTheory.read_bytearray_def;
Theorem write_bytearray_0[simp] = cj 1 write_bytearray_def;
Theorem read_bytearray_1:
  read_bytearray addr 1 getter =
  (case getter addr of NONE => NONE | SOME b => SOME [b])
Proof
  PURE_REWRITE_TAC[ONE] >>
  rw[miscTheory.read_bytearray_def]
QED

Theorem h_prog_skip[simp] = cj 1 h_prog_def;
Theorem pull_ffi_case[simp]:
  f (ffi_result_CASE ffi ret final) =
  ffi_result_CASE ffi (λ x y. f (ret x y)) (f ∘ final)
Proof
  Cases_on ‘ffi’ >> simp[]
QED

(* don't need the one line version now, they are for metatheorems *)
Theorem to_stree_simps[simp] = panItreeSemTheory.to_stree_simps;
Theorem mrec_sem_simps[simp] = panItreeSemTheory.mrec_sem_simps;

val assign_tac = gvs[Once h_prog_def, h_prog_assign_def, eval_def];
val strb_tac = rw[Once h_prog_def, h_prog_store_byte_def];
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

Definition mem_has_word_def:
  mem_has_word mem addr = ∃w. mem (byte_align addr) = Word (w : word32)
End

Definition array:
  array a xs = SEP_ARRAY (λa x. one (a,x)) 1w a xs
End

Definition state_set:
  state_set s = fun2set (s.memory, s.memaddrs)
End

Theorem sep_ldb:
  byte_aligned (addr : word32)
  ∧ (one (addr, Word w) * p) (fun2set (m,dm))
  ⇒ mem_load_byte m dm be addr = SOME (get_byte addr w be)
Proof
  rw[align_thm, mem_load_byte_def] >>
  drule read_fun2set >> rw[]
QED

Theorem sep_strb:
  byte_aligned (addr : word32)
  ∧ (one (addr, Word w) * p) (fun2set (m,dm))
  ⇒ (one (addr, Word (set_byte addr b w be)) * p)
    (fun2set (THE (mem_store_byte m dm be addr b), dm))
Proof
  rw[align_thm, mem_store_byte_def] >>
  drule read_fun2set >> rw[] >>
  metis_tac[write_fun2set, STAR_COMM]
QED

Theorem SEP_T_ID:
  s ⊆ t ∧ p s ⇒ (p * SEP_T) t
Proof
  rw[STAR_def, SPLIT_def, DISJOINT_DEF, SEP_T_def] >>
  rw[EQ_IMP_THM] >>
  (qexistsl_tac [‘s’, ‘t DIFF s’] >>
   fs[SUBSET_DEF, IN_DIFF, IN_INTER, IN_UNION, NOT_IN_EMPTY, EXTENSION] >>
   metis_tac[])
QED

(* SEP_T  -> variable, SEP_W/R_TAC *)
Theorem sep_strb':
  p (fun2set (m,dm DIFF {addr'}))
  ∧ byte_aligned (addr' : word32) ∧ (∃w'. m addr' = Word w') ∧ addr' ∈ dm
  ∧ (p * SEP_T) (fun2set (m,dm))
  ⇒ (p * SEP_T) (fun2set (THE (mem_store_byte m dm be addr' b), dm))
Proof
  rw[align_thm, mem_store_byte_def] >>
  irule SEP_T_ID >>
  qexists_tac ‘(fun2set (m,dm DIFF {addr'}))’ >>
  rw[] >>
  rw[fun2set_def, SUBSET_DEF, combinTheory.UPDATE_APPLY]
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

(* Theorem baseaddr_ref[simp]: *)
(*   to_ffi (itree_mrec h_prog ((Dec name BaseAddr p), s)) *)
(*   = Tau (to_ffi *)
(*          (itree_mrec h_prog *)
(*                      (p,s with locals *)
(*                         := s.locals |+ (name,ValWord s.base_addr)))) ∧ *)
(*   to_ffi (itree_mrec h_prog ((Dec name (Op Add [BaseAddr; Const k]) p), s)) *)
(*   = Tau (to_ffi *)
(*          (itree_mrec h_prog *)
(*                      (p,s with locals *)
(*                         := s.locals |+ (name,ValWord (s.base_addr + k))))) *)
(* Proof *)
(*   fs[eval_def, wordLangTheory.word_op_def, dec_lifted] *)
(* QED *)

(* PURE_ONCE_REWRITE_TAC[ *)
(*       prove(“(iter (muxtx_body s (w2n h)) 0) = *)
(*              (iter (muxtx_body s (w2n h)) (w2n (0w : word32)))”, rw[])] >> *)
(* Globals.max_print_depth := 200; *)

(* write a tactic?
goal = (term list, term)
tactic = goal -> goal list * validation

foo_tac = fn goal => (tactic) goal
*)

(*/
   loops!
 *)

val while_ast = parse_pancake ‘
fun fn(1 dec) {
  var bs = @base;
  @getc(0, 0, @base, 1);
  var i = 0;
  while (1) {
    if (i == 0) {
      @ffi(0, 0, 0, 0);
      i = 1;
    } else {
      @test(0, 0, 0, 0);
      if (lds 1 bs) == 0 {
        return 0;
      }
      st bs, (lds 1 bs) - dec;
      i = 0;
    }
  }
}’;

Definition fun_ast:
  fun_ast (INL [(_,_,args,src)]) = src
End

Definition while_sem_def:
  while_sem (s:('a,'ffi) panItreeSem$bstate) =
  mrec_sem (h_prog (fun_ast ^while_ast,s))
End

Theorem test:
  while_sem s
Proof
QED
