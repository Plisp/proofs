(*
 * actual pancake programs. simps used here
 Globals.max_print_depth := 100
 Cond_rewr.stack_limit := 8
 *)

open stringLib helperLib;
open arithmeticTheory;
open listTheory pairTheory;
open itreeTauTheory;

open panItreeSemTheory;
open panSemTheory; (* eval_def, byte stuff *)
open panLangTheory; (* size_of_shape_def *)
open set_sepTheory;


(* can only load from here XXX bug? *)


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

Theorem itree_wbisim_refl[simp] = itree_wbisim_refl;
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

Theorem h_prog_skip[simp] = cj 1 h_prog_def;
Theorem pull_ffi_case[simp]:
  f (ffi_result_CASE ffi ret final) =
  ffi_result_CASE ffi (λ x y. f (ret x y)) (f ∘ final)
Proof
  Cases_on ‘ffi’ >> simp[]
QED

Theorem mrec_sem_simps[simp] = panItreeSemTheory.mrec_sem_simps;

val assign_tac = gvs[Once h_prog_def, h_prog_assign_def, eval_def];
val strb_tac = rw[Once h_prog_def, h_prog_store_byte_def];

(*
   test
 *)

Definition triple:
  triple inv (p,s) post =
  (∀k. (∀a. post a ⇒ inv (k a))
       ⇒
       inv (mrec_sem (h_prog (p,s)) >>= k))
End

CoInductive silent:
  silent (Ret r) ∧
  (silent t ⇒ silent (Tau t))
End

Theorem silent_tau[simp]:
  silent (Tau t) ⇔ silent t
Proof
  rw[Once silent_cases]
QED

val silent = “silent :(32, β) stree -> bool”
Theorem part1:
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

Theorem part2:
  triple ^silent (panLang$Return (Const 1w),s)
  (λ(r,s). r = SOME (Return (ValWord (1w : word32))))
Proof
  rw[triple] >>
  simp[h_prog_def, h_prog_return_def, eval_def, size_of_shape_def]
QED

Theorem satisfied:
  ^silent (mrec_sem $ h_prog (panLang$Return (Const (1w : word32)),s))
Proof
  assume_tac part2 >>
  fs[triple] >>
  pop_assum $ qspec_then ‘Ret’ strip_assume_tac >> fs[] >>
  pop_assum irule >> rw[] >>
  rw[Once silent_cases]
QED

Theorem mrec_sem_monad_law:
  mrec_sem (ht >>= k)  =  (mrec_sem ht) >>= mrec_sem o k
Proof
  cheat
QED

Theorem join_safe:
  triple ^silent (p1,s) (λrs. if FST rs = NONE then post1 rs else post2 rs) ∧
  (∀rs. post1 rs ⇒ triple ^silent (p2,SND rs) post2)
  ⇒
  triple ^silent (Seq p1 p2,s) post2
Proof
  strip_tac >>
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

(*
 * example!
 * but first I need to prove some nonsense :/
 *)

Definition del_annot_def:
  del_annot (Seq (Annot _ _) (p : 'a panLang$prog)) = del_annot p ∧
  del_annot (Seq a b) = (Seq (del_annot a) (del_annot b)) ∧
  del_annot (Dec vname e p) = (Dec vname e (del_annot p)) ∧
  del_annot (DecCall m s e l p) = (DecCall m s e l (del_annot p)) ∧
  del_annot (If gexp p1 p2) = (If gexp (del_annot p1) (del_annot p2)) ∧
  del_annot (While gexp p) = (While gexp (del_annot p)) ∧
  del_annot p = p
End

Theorem del_annot_seq_id:
  (¬∃a b. p = Annot a b)
  ⇒ del_annot (Seq p q) = Seq (del_annot p) (del_annot q)
Proof
  Cases_on ‘p’ >> rw[del_annot_def]
QED

Theorem prog_induct:
  ∀P.
    P Skip ∧ (∀p. P p ⇒ ∀e m. P (Dec m e p)) ∧
    (∀m e. P (Assign m e)) ∧ (∀e e0. P (Store e e0)) ∧
    (∀e e0. P (StoreByte e e0)) ∧ (∀p p0. P p ∧ P p0 ⇒ P (Seq p p0)) ∧
    (∀p p0. P p ∧ P p0 ⇒ ∀e. P (If e p p0)) ∧
    (∀p. P p ⇒ ∀e. P (While e p)) ∧ P Break ∧ P Continue ∧
    (∀$o l e. P (Call $o e l)) ∧
    (∀p. P p ⇒ ∀l e s m. P (DecCall m s e l p)) ∧
    (∀m e e0 e1 e2. P (ExtCall m e e0 e1 e2)) ∧ (∀m e. P (Raise m e)) ∧
    (∀e. P (Return e)) ∧ (∀ $o m e. P (ShMemLoad $o m e)) ∧
    (∀$o e e0. P (ShMemStore $o e e0)) ∧ P Tick ∧
    (∀m m0. P (Annot m m0))
    ⇒ ∀p. P (p : 'a panLang$prog)
Proof
  strip_tac >>
  qspecl_then [‘P’,‘K T’,‘K T’,‘K T’,‘K T’,‘K T’]
              strip_assume_tac (cj 1 prog_induction) >>
  rw[]
QED

open pred_setTheory set_relationTheory companionTheory;
Theorem whilebody_eq_corres:
  (∀(s :(α, β) bstate). mrec_sem (h_prog (p,s)) ≈ mrec_sem (h_prog (p',s)))
  ⇒ mrec_sem (h_prog (While e p,(s :(α, β) bstate)))
  ≈ mrec_sem (h_prog (While e p',s))
Proof
  rw[h_prog_def, h_prog_while_def] >>
  Cases_on ‘eval (reclock s) e’ >> rw[] >>
  Cases_on ‘x’ >> rw[] >>
  Cases_on ‘w’ >> rw[] >>
  qmatch_goalsub_abbrev_tac ‘mrec_sem (_ >>= k) ≈ mrec_sem (_ >>= k')’ >>
  rw[mrec_sem_monad_law] >>
  ‘{mrec_sem (h_prog (p,s)) >>= mrec_sem ∘ k,
   mrec_sem (h_prog (p',s)) >>= mrec_sem ∘ k'}
            ⊆ rel_to_reln $≈’ suffices_by rw[SUBSET_DEF, rel_to_reln_def] >>
  irule SUBSET_TRANS >>
  qexists_tac ‘λ(a,b).
                 (∃s. a = mrec_sem (h_prog (While e p,s)) ∧
                      b = mrec_sem (h_prog (While e p',s))) ∨
                 (∃t t'. t ≈ t' ∧
                         a = t >>= mrec_sem ∘ k ∧
                         b = t' >>= mrec_sem ∘ k')’ >>
  rw[] >- (metis_tac[]) >>
  rewrite_tac[GSYM wbisim_functional_gfp] >>
  (* enhance avoids getting extra inductive cases on the after_tau! *)
  irule set_param_coind_init >> conj_tac >- rw[] >>
  irule set_param_coind >> conj_tac >- rw[] >>
  qmatch_goalsub_abbrev_tac ‘set_companion _ target’ >>
  rw[SUBSET_DEF, IN_DEF] >> Cases_on ‘x’ >> fs[] >-
   (rw[h_prog_def, h_prog_while_def, SUBSET_DEF] >>
    Cases_on ‘eval (reclock s') e’ >> rw[rel_to_reln_def] >-
     (rw[wbisim_functional_def]) >>
    reverse (Cases_on ‘x’) >> rw[] >- (rw[wbisim_functional_def]) >>
    Cases_on ‘w’ >> rw[mrec_sem_monad_law, wbisim_functional_def] >>
    disj2_tac >> rw[Abbr ‘target’] >>
    irule singleton_subset >>
    irule set_param_coind_done >>
    rw[SUBSET_DEF] >> metis_tac[]) >>
  rw[wbisim_functional_def] >>
  pop_assum (strip_assume_tac o SRULE[Once itree_wbisim_cases]) >-
   (disj2_tac >> fs[Abbr ‘target’] >>
    irule singleton_subset >>
    irule set_param_coind_done >> rw[] >>
    metis_tac[]) >-
   (disj1_tac >> disj2_tac >>
    ‘strip_tau (t >>= mrec_sem ∘ k) (Vis e' (λx. k'' x >>= mrec_sem ∘ k))’
      by metis_tac[itree_bind_vis_strip_tau] >>
    ‘strip_tau (t' >>= mrec_sem ∘ k') (Vis e' (λx. k'³' x >>= mrec_sem ∘ k'))’
      by metis_tac[itree_bind_vis_strip_tau] >>
    qexistsl_tac [‘e'’,‘(λx. k'' x >>= mrec_sem ∘ k)’,
                  ‘(λx. k'³' x >>= mrec_sem ∘ k')’] >>
    rw[] >>
    irule singleton_subset >>
    irule set_param_coind_done >> rw[Abbr ‘target’] >>
    metis_tac[]) >>

  reverse (subgoal ‘(∃r'. strip_tau (Ret r >>= mrec_sem ∘ k) (Ret r') ∧
                          strip_tau (Ret r >>= mrec_sem ∘ k') (Ret r')) ∨
                    ∃t'' t'³'.
                      (Ret r >>= mrec_sem ∘ k = Tau t'' ∧
                       Ret r >>= mrec_sem ∘ k' = Tau t'³') ∧
                      (t'',t'³') ∈ set_companion wbisim_functional target’) >-
   (disj2_tac >>
    qpat_assum ‘strip_tau t _’ mp_tac >>
    Induct_on ‘strip_tau’ >> rw[] >-
     (fs[] >>
      irule singleton_subset >>
      irule set_param_coind_upto >> rw[] >>
      qexists_tac ‘after_taus_func’ >>
      rw[in_after_taus_func] >>
      irule after_taus_tauL >>
      irule after_taus_rel >> rw[]) >>
    qpat_assum ‘strip_tau t' _’ mp_tac >>
    Induct_on ‘strip_tau’ >> rw[] >-
     (fs[] >>
      irule singleton_subset >>
      irule set_param_coind_upto >> rw[] >>
      qexists_tac ‘after_taus_func’ >>
      rw[in_after_taus_func] >>
      irule after_taus_tauR >>
      irule after_taus_rel >> rw[]) >>
    fs[]) >-
   (metis_tac[itree_bind_resp_t_wbisim, itree_wbisim_strip_tau_Ret,
              itree_wbisim_sym, itree_wbisim_strip_tau_sym, itree_wbisim_refl]) >>
  rw[Abbr ‘k’, Abbr ‘k'’] >>
  Cases_on ‘r’ >> rw[] >>
  Cases_on ‘q’ >> rw[] >-
   (disj2_tac >>
    irule singleton_subset >>
    irule set_param_coind_done >> rw[Abbr ‘target’] >>
    metis_tac[]) >>
  Cases_on ‘x’ >> rw[] >>
  (disj2_tac >>
   irule singleton_subset >>
   irule set_param_coind_done >> rw[Abbr ‘target’] >>
   metis_tac[])
QED

Theorem del_annot_corres:
  mrec_sem (h_prog (del_annot ast,s)) ≈ mrec_sem (h_prog (ast,s))
Proof
  qid_spec_tac ‘s’ >>
  qid_spec_tac ‘ast’ >>
  recInduct prog_induct >>
  rw[del_annot_def] >-
   (rw[h_prog_def, h_prog_dec_def] >>
    Cases_on ‘eval (reclock s) e’ >> rw[] >>
    rw[mrec_sem_monad_law] >>
    irule itree_bind_resp_wbisim >> fs[]) >-
   (Cases_on ‘∃a b. p = Annot a b’ >> rw[] >-
     (fs[h_prog_seq_def, h_prog_def, del_annot_def]) >>
    fs[del_annot_seq_id] >>
    rw[h_prog_def, h_prog_seq_def, del_annot_def] >>
    rw[mrec_sem_monad_law] >>
    irule itree_bind_resp_wbisim >> rw[] >>
    Cases_on ‘r’ >> rw[]) >-
   (rw[h_prog_def, h_prog_cond_def] >>
    Cases_on ‘eval (reclock s) e’ >> rw[] >>
    Cases_on ‘x’ >> rw[] >>
    Cases_on ‘w’ >> rw[]) >-
   (metis_tac[whilebody_eq_corres]) >-
   (rw[h_prog_def, h_prog_deccall_def] >>
    Cases_on ‘eval (reclock s') e’ >> rw[] >>
    Cases_on ‘x’ >> rw[] >>
    Cases_on ‘w’ >> rw[] >>
    Cases_on ‘OPT_MMAP (eval (reclock s')) l’ >> rw[] >>
    Cases_on ‘lookup_code s'.code m' x’ >> rw[] >>
    Cases_on ‘x'’ >> rw[] >>
    rw[mrec_sem_monad_law] >>
    irule itree_bind_resp_wbisim >> rw[] >>
    Cases_on ‘r'’ >> Cases_on ‘q'’ >-
     (rw[h_handle_deccall_ret_def]) >>
    Cases_on ‘x'’ >> rw[h_handle_deccall_ret_def] >>
    rw[mrec_sem_monad_law] >>
    irule itree_bind_resp_wbisim >>
    rw[])
QED

(* program *)

open panPtreeConversionTheory; (* parse_funs_to_ast *)
val while_ast = parse_pancake ‘
fun fn(1 i) {
  var n = 0;
  while(i > 0) {
    n = n + i;
    i = i - 1;
  }
  return n;
}’;

val while_noannot = rhs $ concl $ SRULE[] $ EVAL “del_annot (fun_ast ^while_ast)”;

Definition while_sem_def:
  while_sem (s:('a,'ffi) panItreeSem$bstate) =
  mrec_sem (h_prog (^while_noannot,s))
End

Theorem test:
  while_sem s = ARB
Proof
  rw[while_sem_def, fun_ast] >>
  rw[]
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
