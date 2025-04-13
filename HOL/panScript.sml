(*
 * actual pancake programs. simps used here
 Globals.max_print_depth := 100
 Cond_rewr.stack_limit := 8
 *)

open stringLib helperLib; (* String *)
open arithmeticTheory; (* ONE *)
open pairTheory;
(* open pred_setTheory set_relationTheory fixedPointTheory companionTheory; *)
open itreeTauTheory;

open ffiTheory; (* ffiname *)
open panSemTheory; (* eval_def, byte stuff *)
open panLangTheory; (* size_of_shape_def *)
open panPtreeConversionTheory; (* parse_funs_to_ast *)
open panItreeSemTheory panItreePropsTheory;
(* open set_sepTheory; *)

val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>="[local] = “itree_bind”;

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
    rhs $ concl $ SRULE[] $ EVAL “(parse_funs_to_ast ^code)”
end

fun parse_pancake_nosimp q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “(parse_funs_to_ast ^code)”
end

Definition fun_ast:
  fun_ast (INL [(_,_,args,src)]) = src
End

(* add_user_printer docs, sml-mode *)
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

Theorem pull_ffi_case[simp]:
  f (ffi_result_CASE ffi ret final) =
  ffi_result_CASE ffi (λ x y. f (ret x y)) (f ∘ final)
Proof
  Cases_on ‘ffi’ >> simp[]
QED

Theorem pan_eval_simps[simp]:
    eval s (Const w) = SOME (ValWord w)
  ∧ eval s (Var v) = FLOOKUP s.locals v
  ∧ eval s BaseAddr = SOME (ValWord s.base_addr)
  ∧ eval s (Label fname) = OPTION_IGNORE_BIND (FLOOKUP s.code fname)
                                              (SOME (ValLabel fname))
  ∧ eval s (BytesInWord :32 exp) = SOME (ValWord 4w)
Proof
  rw[eval_def] >>
  Cases_on ‘FLOOKUP s.code fname’ >> rw[byteTheory.bytes_in_word_def]
QED

Theorem apply_update_simp[simp] = cj 1 combinTheory.UPDATE_APPLY;
(* may explode cases if k1 = k2 isn't decidable: luckily we cmp names = strings *)
Theorem do_flookup_simp[simp] = finite_mapTheory.FLOOKUP_UPDATE;
Theorem valid_value_simp[simp] = is_valid_value_def;
Theorem shape_of_simp[simp] = shape_of_def;

Theorem read_bytearray_0[simp] = cj 1 miscTheory.read_bytearray_def;
Theorem write_bytearray_0[simp] = cj 1 write_bytearray_def;
Theorem read_bytearray_1:
  read_bytearray addr 1 getter =
  (case getter addr of NONE => NONE | SOME b => SOME [b])
Proof
  PURE_REWRITE_TAC[ONE] >>
  rw[miscTheory.read_bytearray_def]
QED

Theorem mrec_sem_simps[simp] = panItreeSemTheory.mrec_sem_simps;

(*
 * TODO
 *)

val ffi_ast = parse_pancake ‘
fun f() {
  @read(0,0,@base,1);
  @write(@base,1,0,0);
}’;

val ffi_noannot =
  rhs $ concl $ SRULE[]
      $ INST_TYPE [alpha |-> ``: 32``] $ EVAL “del_annot (fun_ast ^ffi_ast)”;

(* box modality *)
Definition next_def:
  next tr (dev,s) (array_ptr,e)
          (post :γ -> 32 result option -> (32, α) bstate
                   -> (32, α) stree -> bool)
          (t : (32, α) stree) =
  (∀a dev'.
     tr dev (e,a) dev' ⇒
     (∃(k : 'a ffi_result -> (32, α) stree).
        strip_tau t (Vis e k) ∧
        case a of
          FFI_final a => ARB
        | FFI_return ffi bytes
          => post dev' NONE
                  (s with <|memory := write_bytearray array_ptr bytes
                                      s.memory s.memaddrs s.be; ffi := ffi|>)
                  (k a)))
End

Theorem test:
  (∀(dev : 'b) r s.
     r = NONE ∧ mem_load_byte s.memory s.memaddrs s.be s.base_addr = SOME 0w
     ⇒ P dev r s (Tau (k (r,s)))) ∧
  mem_load_byte s.memory s.memaddrs s.be s.base_addr = SOME b ⇒
  next (λ_ (e,a) _. ∃ffi. a = FFI_return ffi [0w])
       ((), s)
       (s.base_addr, (FFI_call (ExtCall "read") [] [b]))
       P
       (Tau
        (mrec_sem
         (h_prog (ExtCall «read» (Const 0w) (Const 0w) BaseAddr (Const 1w),s))
         >>= k))
Proof
  rw[h_prog_def, h_prog_ext_call_def, read_bytearray_1] >>
  rw[next_def] >> rw[] >>
  last_x_assum irule >> rw[] >>
  cheat
QED

Theorem test2:
  mem_load_byte s.memory s.memaddrs s.be s.base_addr = SOME 0w ⇒
  next (λ_ (e,a) _. ∃ffi. a = FFI_return ffi [0w])
       ((), s)
       (s.base_addr, (FFI_call (ExtCall "write") [0w] []))
       (λdev r s t. r = NONE)
       (Tau (Tau (mrec_sem
        (h_prog (ExtCall «write» BaseAddr (Const 1w) (Const 0w) (Const 0w),
                 (s : (32,'a) bstate))))))
Proof
  rw[h_prog_def, h_prog_ext_call_def, read_bytearray_1] >>
  rw[next_def] >> rw[]
QED

Theorem testseq:
  mem_load_byte s.memory s.memaddrs s.be s.base_addr = SOME b ⇒
  next (λ_ (e,a) _. ∃ffi b. a = FFI_return ffi [0w])
       ((), s)
       (s.base_addr, (FFI_call (ExtCall "read") [] [b]))
       (λdev' r s' t.
          next (λ_ (e,a) _. ∃ffi. a = FFI_return ffi [0w])
               ((), s')
               (s'.base_addr, (FFI_call (ExtCall "write") [0w] []))
               (λdev r _ _. r = NONE)
               t)
       (mrec_sem (h_prog (^ffi_noannot,s)))
Proof
  rw[Once h_prog_def, h_prog_seq_def] >>
  qmatch_goalsub_abbrev_tac ‘next _ _ _ P’ >>
  rw[mrec_sem_monad_law] >>
  qmatch_goalsub_abbrev_tac ‘mrec_sem _ >>= k’ >>
  irule test >> rw[Abbr ‘P’, Abbr ‘k’] >>
  irule test2 >> rw[]
QED

(* coinductive example: random register
 *
 * note: Devices may make silent transitions and may race with the driver,
 *       so then composition of driver and device is not then a deterministic
 *       function of the env and so cannot represented as an itree.
 *
 * let's split the proof into
 * 1) the program follows the protocol (all events have a valid device answer)
 *    - implicit in specification, needs to be proved separately
 * 2) the program is correct on all traces assuming the device follows protocol
 *)

val reg_ast = parse_pancake ‘
fun reg() {
  while(1) {
    @read(0,0,@base,1);
    @write(@base,1,0,0);
  }
}’;

val reg_annot = rhs $ concl $ SRULE[]
                    $ INST_TYPE [alpha |-> ``:32``] $ EVAL “(fun_ast ^reg_ast)”;
val reg_noannot =
  rhs $ concl $ SRULE[]
      $ INST_TYPE [alpha |-> ``: 32``] $ EVAL “del_annot (fun_ast ^reg_ast)”;

(* LTS describing valid device returns, currently no silent transitions *)
Inductive rand:
  rand b (FFI_call (ffi$ExtCall "read") [] [_], FFI_return f [b]) b' ∧
  rand b (FFI_call (ffi$ExtCall "write") [a] [], FFI_return f []) a
End

CoInductive reg_spec:
  (reg_spec dev (t : (32,'b) stree) ∧
   (∀b.
      t' ≈ (Vis e1 k) ∧ e1 = (FFI_call (ffi$ExtCall "read") [] [a]) ∧
      ∀ans. rand dev (e1,ans) dev'
            ⇒
            k ans = Vis e2 (λ_. t) ∧ e2 = (FFI_call (ffi$ExtCall "write") [b] []) ∧
            rand dev' (e2,ans2) dev''
   )
   ⇒
   reg_spec dev'' t')
  ∧
  (reg_spec dev t ⇒ reg_spec dev (Tau t))
End

Theorem reg_spec_tau:
  ∀t. reg_spec (Tau t) = reg_spec t
Proof
  rw[Once reg_spec_cases]
QED

Theorem test:
  mem_load_byte s.memory s.memaddrs s.be s.base_addr = SOME b ⇒
  reg_spec (mrec_sem (h_prog (^reg_noannot,s)))
Proof
  assume_tac reg_spec_tau >> strip_tac >>
  rw[h_prog_def, h_prog_while_def, eval_def, h_prog_seq_def] >>
  rw[h_prog_def, h_prog_ext_call_def, eval_def, read_bytearray_1] >>
  irule reg_spec_coind >>

  qexists_tac ‘λt.
                 ∃s'. t = untau $ mrec_sem
                          (h_prog
                           (While (Const 1w)
                                  (Seq
                                   (ExtCall «read» (Const 0w) (Const 0w) BaseAddr
                                            (Const 1w))
                                   (ExtCall «write» BaseAddr (Const 1w) (Const 0w)
                                            (Const 0w))),s'))’ >>
  rw[] >- (rw[h_prog_def, h_prog_while_def, eval_def, untau] >> metis_tac[]) >>
  disj1_tac >>
  rw[h_prog_def, h_prog_while_def, eval_def, untau, h_prog_seq_def] >>
  rw[h_prog_def, h_prog_ext_call_def, eval_def, read_bytearray_1] >>
  qexists_tac ‘ARB’ >>
  rw[FUN_EQ_THM] >- cheat >>
  (rw[h_prog_def, h_prog_ext_call_def, eval_def, read_bytearray_1] >>
   qabbrev_tac ‘e = mem_load_byte
                  (write_bytearray (s :(32, α) bstate).base_addr [(w :word8)]
                     s.memory s.memaddrs s.be) s.memaddrs s.be s.base_addr’ >>
   ‘e = SOME w’ by cheat >>
   rw[] >>
   irule itree_wbisim_vis >> rw[] >>
   Cases_on ‘r’ >> rw[] >-
    (cheat
    )
  )
QED











(*
 * hmm, this is suitable for global invariants but not quite
 *)

Definition triple:
  triple inv (p,s) post =
  (∀k. (∀rs. post rs ⇒ inv (k rs))
       ⇒
       inv (mrec_sem (h_prog (p,s)) >>= k))
End

Definition resp_wbisim_def:
  resp_wbisim P = (∀t t'. t ≈ t' ⇒ P t ⇒ P t')
End

Theorem resp_wbisim_tau:
  resp_wbisim P ⇒ (P (Tau t) ⇔ P t)
Proof
  rw[resp_wbisim_def] >>
  metis_tac[itree_wbisim_tau_eq, itree_wbisim_sym]
QED

val P = “P :(32, β) stree -> bool”;
Theorem seq_triple:
  (∀t. P (Tau t) = (P t)) ∧
  triple ^P (p1,s) (λrs. if FST rs = NONE then post1 rs else post2 rs) ∧
  (∀rs. post1 rs ⇒ triple ^P (p2,SND rs) post2)
  ⇒
  triple ^P (Seq p1 p2,s) post2
Proof
  rw[triple] >>
  rw[h_prog_def, h_prog_seq_def] >>
  rw[mrec_sem_monad_law] >>
  fs[triple] >>
  rw[itree_bind_assoc] >>
  last_assum irule >>
  Cases >> rename1 ‘post1 (res,s')’ >>
  rw[] >>
  metis_tac[FST,SND]
QED

Theorem dec_triple:
  (∀t. P (Tau t) = (P t)) ∧
  eval (reclock s) e = SOME val ∧
  triple ^P (p,s with locals := s.locals |+ (vname,val))
         (λ(r,s'). post (r, s' with locals :=
                            res_var s'.locals (vname,FLOOKUP s.locals vname)))
  ⇒
  triple ^P (Dec vname e p,s) post
Proof
  rw[triple] >>
  rw[h_prog_def, h_prog_dec_def] >>
  rw[mrec_sem_monad_law] >>
  rw[itree_bind_assoc] >>
  last_assum irule >>
  Cases >> rw[]
QED

(*
 * predicate for backwards proof:
 * if inv holds in all branches satisfying the postcondition, then it holds here
 *
 * weird: if post can be made to hold in all Ret branches, then it holds here
 *)

CoInductive silent:
  silent (Ret r) ∧
  (silent t ⇒ silent (Tau t))
End

Theorem silent_resp:
  resp_wbisim silent
Proof
  rw[resp_wbisim_def] >>
  irule silent_coind >>
  qexists_tac ‘λt'. ∃t. t ≈ t' ∧ silent t’ >>
  rw[] >- (metis_tac[]) >>
  Cases_on ‘a0’ >> rw[] >-
   (metis_tac[itree_wbisim_trans, itree_wbisim_tau_eq]) >>
  ntac 2 (last_x_assum kall_tac) >>
  gvs[Once itree_wbisim_cases, Once silent_cases] >>
  pop_assum mp_tac >> pop_last_assum mp_tac >>
  Induct_on ‘strip_tau’ >> rw[] >>
  rw[Once silent_cases]
QED

Theorem silent_tau[simp]:
  silent (Tau t) ⇔ silent t
Proof
  metis_tac[silent_resp, resp_wbisim_tau]
QED

val silent = “silent :(32, β) stree -> bool”
Theorem spin_silent:
  triple ^silent (panLang$While (Const 1w) Skip,s) (K F)
Proof
  rw[triple] >>
  irule silent_coind >>
  qexists_tac ‘λt. t = (mrec_sem (h_prog (While (Const 1w) Skip,s))) >>= k ∨
                   t = Tau (mrec_sem (h_prog (While (Const 1w) Skip,s)) >>= k)’ >>
  rw[Once h_prog_def] >>
  disj2_tac >>
  simp[SimpL “$=”, h_prog_while_def, eval_def] >>
  ‘1 ≠ 0 MOD dimword (:32)’ by EVAL_TAC >>
  rw[]
QED

(* weird case found by Johannes: k now needs to 'fix' the return postcondition
 * This also cannot happen in an infinite case since we must prove the invariant
 * holds of (inf >>= k) = inf given pred (k r) for some arbitrary function k
 * which is only possible if the itree domain is very small *)

CoInductive silent':
  silent' (Ret (SOME (Return (ValWord 2w)))) ∧
  (silent' t ⇒ silent' (Tau t))
End

Theorem satisfied:
  triple silent' (panLang$Return (Const 1w),s)
  (λ(r,s). r = SOME (Return (ValWord (1w : word32))))
Proof
  rw[triple] >>
  simp[h_prog_def, h_prog_return_def, eval_def] >>
  rw[size_of_shape_def]
QED

(*
 * example: inductive predicate
 *)

val while_ast = parse_pancake ‘
fun tri(1 i) {
  var n = 0;
  while(i > 0) {
    n = n + i;
    i = i - 1;
  }
  return n;
}’;

val while_annot = rhs $ concl $ SRULE[] $ EVAL “(fun_ast ^while_ast)”;
val while_noannot = rhs $ concl $ SRULE[] $ EVAL “del_annot (fun_ast ^while_ast)”;

Definition while_sem_def:
  while_sem (s:('a,'ffi) panItreeSem$bstate) =
  mrec_sem (h_prog (^while_annot,s))
End

Definition tri_def:
  tri 0 = 0 ∧
  tri (SUC n) = SUC n + (tri n)
End

Inductive correct:
  correct i ((Ret (SOME (Return (ValWord (n2w (tri i)))) , s)) : (32, 'b) stree) ∧
  (correct i t ⇒ correct i (Tau t))
End

Theorem correct_resp:
  resp_wbisim (correct i)
Proof
  simp[resp_wbisim_def] >>
  Induct_on ‘correct’ >> simp[] >>
  simp[Once itree_wbisim_cases] >>
  Induct_on ‘strip_tau’ >> rw[] >>
  rw[Once correct_cases]
QED

Theorem correct_tau[simp]:
  correct i (Tau t) ⇔ correct i t
Proof
  rw[Once correct_cases]
QED

Theorem while_body_triple:
  triple (correct i)
  (While (Cmp Less (Const (0w : word32)) (Var «i»))
         (Seq (Assign «n» (Op Add [Var «n»; Var «i»]))
              (Assign «i» (Op Sub [Var «i»; Const 1w]))),
   s with locals :=
   s.locals
    |+ («i»,ValWord (n2w (i - k)))
    |+ («n»,ValWord (n2w (tri i - tri (i - k)))))
  (λrs.
     if FST rs = NONE then
       (λ(r,s). FLOOKUP s.locals «n» = SOME (ValWord (n2w (tri i))))
       rs
     else F)
Proof
  rw[triple] >>
  Induct_on ‘i - k’ >> rw[] >-
   (‘i - k = 0’ by rw[] >>
    pop_assum $ rw o single >>
    rw[tri_def] >>
    rw[h_prog_def, h_prog_while_def, eval_def, asmTheory.word_cmp_def]) >>
  ‘(0w : word32) < n2w (i − k)’ by cheat >>
  rw[h_prog_def, h_prog_while_def, eval_def, asmTheory.word_cmp_def] >>
  rw[h_prog_seq_def] >>
  rw[h_prog_def, h_prog_assign_def, eval_def, wordLangTheory.word_op_def] >>
  ‘n2w (i - k) + (-1w : word32) = n2w (i - (k + 1))’ by cheat >>
  pop_assum $ rw o single >>
  ‘(n2w (i − k) : word32) + n2w (tri i − tri (i − k))
   = n2w (tri i − tri (i − (k + 1)))’ by cheat >>
  pop_assum $ rw o single >>
  qmatch_goalsub_abbrev_tac ‘h_prog_while _ _ st’ >>
  ‘st = s with locals := s.locals |+ («i»,ValWord (n2w (i − (k + 1)))) |+
                          («n»,ValWord (n2w (tri i − tri (i − (k + 1)))))’
    by cheat >>
  pop_assum $ rw o single >>
  rw[GSYM h_prog_def]
QED

Theorem while_seq_triple:
  triple (correct i)
         (Seq
          (While (Cmp Less (Const (0w : word32)) (Var «i»))
                 (Seq (Assign «n» (Op Add [Var «n»; Var «i»]))
                      (Assign «i» (Op Sub [Var «i»; Const 1w]))))
          (Return (Var «n»)),
          (s with locals := s.locals |+ («i», ValWord (n2w i)) |+ («n»,ValWord 0w)))
         (λ(r,s). r = SOME (Return (ValWord (n2w (tri i)))))
Proof
  irule seq_triple >> rw[] >>
  qexists_tac ‘λ(r,s). FLOOKUP s.locals «n» = SOME (ValWord (n2w (tri i)))’ >>
  rw[] >-
   (Cases_on ‘rs’ >> fs[triple] >>
    rw[h_prog_def, h_prog_return_def, eval_def, size_of_shape_def]) >>

  assume_tac (GEN_ALL while_body_triple) >>
  pop_assum $ qspecl_then [‘s’, ‘0’, ‘i’] strip_assume_tac >>
  fs[triple]
QED

Theorem while_triple:
  triple (correct i)
         (Dec «n» (Const (0w : word32))
              (Seq
               (While (Cmp Less (Const 0w) (Var «i»))
                      (Seq (Assign «n» (Op Add [Var «n»; Var «i»]))
                           (Assign «i» (Op Sub [Var «i»; Const 1w]))))
               (Return (Var «n»))),
          (s with locals := s.locals |+ («i», ValWord (n2w i))))
         (λ(r,s). r = SOME (Return (ValWord (n2w (tri i)))))
Proof
  irule dec_triple >> rw[eval_def] >>
  assume_tac while_seq_triple >> rw[]
QED

Theorem while_correct:
  correct i (while_sem (s with locals := s.locals |+ («i», ValWord (n2w i))))
Proof
  irule (SRULE[resp_wbisim_def] correct_resp) >>
  rw[while_sem_def] >>
  irule_at Any del_annot_corres >>
  rw[del_annot_def] >>
  rw[while_sem_def] >>
  assume_tac while_triple >>
  fs[triple] >>
  pop_assum $ qspec_then ‘Ret’ strip_assume_tac >> fs[] >>
  pop_assum irule >>
  rw[Once correct_cases, ELIM_UNCURRY] >>
  Cases_on ‘a’ >> fs[]
QED






























(*/ word nonsense TODO setsep check notebook
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
