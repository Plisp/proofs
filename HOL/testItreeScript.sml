(*
 * Coinductive semantics with interaction trees!
 *
 * Directly express an infinite tree program-semantics structure via continuations.
 * By developing an algebra, reasoning can be mostly done above the Tau level,
 * which are convenient for expressing silent program steps which may differ
 * depending on context. Taus are necessary in the semantics, as termination of
 * of loops cannot determined ahead of time but we need productivity for soundness.
 * Oracle queries are encoded by answer branching and 'evaluating' in a context where the
 * responses are limited, we can simulate interaction with external devices.
 *
 * Itrees make the nondeterminism external to the structure: this seems like a better fit
 * for mix-and-match with sets of restrictions on interactions - device models - though
 * another approach would be to just shove the device in the ffi state and work with traces?
 * One thing to note with HOL4 is that response types can't be restricted per event
 * constructor as they can with dependent types, but this turns out to be insufficient
 * anyways since we want to restrict responses further by a possibly nondeterministic device
 * and at the same time prove that pancake program upholds its part of the protocol.
 *
 * In comparision to the clock approach in cakeML's FBS semantics, there is less
 * distinction between finite|infinite programs, usually allowing local reasoning.
 * Consider this an equivalent representation more suited to program reasoning, as
 * opposed to compiler correctness proofs.
 *
 * detail: fix_clock is necessary in proofs as with induction on e.g.(Seq p1 p2)
 * to prove productivity we need to adjust the clock of p2 to start from the
 * amount after running p1.
 *
 * specifications should be *structural*, in terms of observable interaction rather
 * than detailing implementation. but proofs should be *syntax-directed*
 *)

(* XXX can't enable types. show_types := true *)

open stringLib; (* parsing, text examples etc. *)
open llistTheory itreeTauTheory;

open relationTheory;

Overload emit[local] = “itree_trigger”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>="[local] = “itree_bind”;
Overload iter[local] = “itree_iter”;

(* open monadsyntax; *)
(* val _ = *)
(*     monadsyntax.declare_monad ( *)
(*       "itree_monad", *)
(*       { bind = “itree_bind”, ignorebind = NONE, unit = “Ret”, *)
(*         guard = NONE, choice = NONE, fail = NONE} *)
(*     ) *)
(* val _ = monadsyntax.temp_enable_monad "itree_monad"; *)

val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;

(*
 * transition relation and initial state
 * success: expressed in predicates themselves
 * carrier: not needed, use type
 *)
Type lts[pp] = “:((α # β option # α -> bool) # α)”;

Definition lts_rel[simp]:
  lts_rel ((r,i) : ('s,'a) lts) = r
End
Definition lts_init[simp]:
  lts_init ((r,i) : ('s,'a) lts) = i
End

(* CSP || operator
 *
 * note: the LTS event type is more general than (e,a)
 * note: competing processes should not communicate directly
 *
 * TODO shallow-embedded channel syntax
 *)

Definition comm_rel_l:
  comm_rel_l com r = { ((s,t), a, (s',t')) | a ∉ com ∧ (s,a,s') ∈ r ∧ t = t' }
End

Definition comm_rel_r:
  comm_rel_r com r' = { ((s,t), a, (s',t')) | a ∉ com ∧ (t,a,t') ∈ r'∧ s = s' }
End

Theorem comm_rel_r_lift:
  ((s,t),a,(s',t')) ∈ comm_rel_r com r' ⇔ a ∉ com ∧ (t,a,t') ∈ r' ∧ s = s'
Proof
  rw[comm_rel_r] >> metis_tac[]
QED

Definition comm_rel_com:
  comm_rel_com com r r' = { ((s,t), a, (s',t')) | a ∉ com ∧ (t,a,t') ∈ r'∧ s = s' }
End

Definition comm_rel:
  comm_rel com r r' = comm_rel_l com r ∪ comm_rel_r com r' ∪ comm_rel_com com r r'
End

Definition comm:
  comm com ((r,i) : ('s,'a) lts) ((r',i') : ('t,'a) lts) =
  (comm_rel com r r', (i,i'))
End

Definition par:
  par l1 l2 = comm ∅ l1 l2
End

Definition stop:
  stop s = ({}, s)
End

Definition prefix:
  prefix i' a ((r,i) : ('s,'a) lts) = (r ∪ {(i',a,i)},i')
End

(* this is more natural than restriction *)
Definition hide:
  hide ((r,i) : ('s,'a) lts) a =
  ({ (s,NONE,s') | (s,a,s') ∈ r } ∪ { (s,a',s') | a' ≠ a ∧ (s,a',s') ∈ r }, i)
End

Definition choice_ext:
  choice_ext (s : 's) (act_lts : 'a option -> ('s,'a) lts -> bool)
  = (BIGUNION { r | ∃a i. act_lts a (r,i) } ∪ { (s,a,i) | ∃r. act_lts a (r,i) }, s)
End

Definition choice_int:
  choice_int s ltsfam = choice_ext s (λao lts. ao = NONE ∧ lts ∈ ltsfam)
End

(* monad *)
Definition seq:
  seq ((r,i) : ('s,'a) lts) (final : 's -> bool) (next : 's -> ('s,'a) lts) =
  (r ∪ { (fs,NONE,lts_init (next fs)) | final fs }
     ∪ BIGUNION { lts_rel (next s) | final s },
   i)
End

Definition fix:
  fix ((r,i) : ('s,'a) lts) (final : 's -> bool)
  = seq (r,i) final (K (r,i))
End

(* the equivalence of choice: weak bisimulation, a congruence for csp
 * more fine than trace equivalence for dealing with liveness
 *)
Definition lts_taus:
  lts_taus r = RTC (λs t. r (s,NONE,t))
End

(* ⇒ -a-> ⇒ *)
Definition lts_wts:
  lts_wts r a = lts_taus r O (λs t. r (s,a,t)) O lts_taus r
End

CoInductive lts_wbisim:
  ((∀s' a. a ≠ NONE ∧ r (s,a,s') ⇒ ∃t'. lts_wts r' a t t' ∧ lts_wbisim r r' s' t') ∧
   (∀t' a. a ≠ NONE ∧ r'(t,a,t') ⇒ ∃s'. lts_wts r  a s s' ∧ lts_wbisim r r' s' t') ∧
   (∀s'. r  (s,NONE,s') ⇒ ∃t'. lts_taus r' t t' ∧ lts_wbisim r r' s' t') ∧
   (∀t'. r' (t,NONE,t') ⇒ ∃s'. lts_taus r  s s' ∧ lts_wbisim r r' s' t')
   ⇒ lts_wbisim r r' s t)
End

Theorem lts_wbisim_refl[simp]:
  lts_wbisim r r s s
Proof
  irule lts_wbisim_coind >>
  qexists_tac ‘λs s'. s = s'’ >>
  rw[] >-
   (rw[lts_wts, relationTheory.O_DEF] >>
    metis_tac[lts_taus, RTC_cases]) >-
   (rw[lts_wts, relationTheory.O_DEF] >>
    metis_tac[lts_taus, RTC_cases]) >-
   (rw[lts_taus])
QED

Theorem lts_wbisim_sym:
  lts_wbisim r r' s t ⇒ lts_wbisim r' r t s
Proof
  strip_tac >>
  irule lts_wbisim_coind >>
  qexists_tac ‘λt s. lts_wbisim r r' s t’ >>
  rw[] >>
  last_x_assum kall_tac >>
  last_x_assum $ strip_assume_tac o SRULE[Once lts_wbisim_cases] >> fs[]
QED

fun pat_rw thms pat = qpat_assum pat $ strip_assume_tac o SRULE thms;

Theorem lts_ets_to_ets:
  lts_wbisim r' r'' t u ∧
  lts_taus r' t t'
  ⇒ ∃u'.
      lts_wbisim r' r'' t' u' ∧
      lts_taus r'' u u'
Proof
  (* induct on RTC of ets *)
  cheat
QED

Theorem lts_wts_to_wts:
  lts_wbisim r' r'' t u ∧
  lts_wts r' a t t'
  ⇒ ∃u'.
      lts_wbisim r' r'' t' u' ∧
      lts_wts r'' a u u'
Proof
  (* induct on RTC of wts *)
  cheat
QED

Theorem lts_wbisim_trans:
  lts_wbisim r r' s t ∧ lts_wbisim r' r'' t u ⇒ lts_wbisim r r'' s u
Proof
  rw[] >>
  irule lts_wbisim_coind >>
  qexists_tac ‘λs u. ∃t. lts_wbisim r r' s t ∧ lts_wbisim r' r'' t u’ >>
  reverse conj_tac >- (metis_tac[]) >>
  ntac 2 (pop_assum kall_tac) >>
  ntac 2 strip_tac >>
  rename1 ‘_ s u ⇒ _’ >>
  rw[] >-
   (pat_rw[Once lts_wbisim_cases] ‘lts_wbisim r r' _ _’ >>
    ntac 2 $ qpat_x_assum ‘∀_. _ ⇒ _’ kall_tac >>
    first_x_assum drule_all >> rw[] >>
    pat_rw[Once lts_wbisim_cases] ‘lts_wbisim r' r'' _ _’ >>
    ntac 2 $ qpat_x_assum ‘∀_. _ ⇒ _’ kall_tac >>
    drule_all lts_wts_to_wts >> rw[] >>
    metis_tac[]) >-
   (rename1 ‘r'' (u,a,u')’ >> cheat) >-
   (pat_rw[Once lts_wbisim_cases] ‘lts_wbisim r r' _ _’ >>
    ntac 2 $ qpat_x_assum ‘∀_ _. _ ⇒ _’ kall_tac >>
    first_x_assum drule >> rw[] >>
    pat_rw[Once lts_wbisim_cases] ‘lts_wbisim r' r'' _ _’ >>
    ntac 2 $ qpat_x_assum ‘∀_ _. _ ⇒ _’ kall_tac >>
    drule_all lts_ets_to_ets >> rw[] >>
    metis_tac[]) >-
   (rename1 ‘r'' (u,NONE,u')’ >> cheat)
QED

(*
 * example interpreting itrees into labelled transition systems
 *)
CoInductive subtree:
[~tau:]
  (subtree t s ⇒ subtree (Tau t) s)
[~vis:]
  (subtree (k a) s ⇒ subtree (Vis e k) s)
[~id:]
  (subtree t t)
End

Theorem subtree_trans:
  subtree s r ∧ subtree t s ⇒ subtree t r
Proof
  strip_tac >>
  irule subtree_coind >>
  qexists_tac ‘λt' r'. ∃s'. subtree t' s' ∧ subtree s' r'’ >>
  reverse (rw[]) >- (metis_tac[]) >>
  ntac 2 (last_x_assum kall_tac) >>
  Cases_on ‘a0’ >> metis_tac[subtree_cases]
QED

Inductive itree_rel:
  itree_rel (Tau t, NONE, t) ∧
  itree_rel (Vis e k, SOME (e,a), (k a))
End

Definition itree_sm_def:
  itree_sm (t : ('a,'e,'r) itree)
  = (subtree t,
     itree_rel : ('a,'e,'r) itree # ('e # 'a) option # ('a,'e,'r) itree -> bool,
     t)
End

(* the producer produces buffers (represented as numbers / pointers)
 * and can sometimes stop in the false state.
 * Meanwhile the consumer receives and sends them
 *)

Datatype:
  testev = Produce num | Recv | Send num
End

(* Definition prod'_def: *)
(*   prod' = ({ (T,SOME(Recv,Produce n),T) | n < 256 } ∪ {(T,NONE,F)}, T) *)
(*         : (bool, testev # testev) lts *)
(* End *)

(* (* sanity check: we can continuously produce the 0 pointer *) *)
(* Theorem test_okpath: *)
(*   okpath (curry3 (lts_rel prod')) *)
(*          (unfold (λ_. T) (λ_. SOME ((),SOME (Recv,Produce 0))) ()) *)
(* Proof *)
(*   irule okpath_unfold >> *)
(*   qexists_tac ‘K T’ >> *)
(*   rw[prod'_def] *)
(* QED *)

Datatype:
  prod_states = Start | Producing num | After num | Exit
End

Definition prod_def:
  prod = fix
         (choice_int Start
                     ({prefix (Producing n) (SOME (Recv,Produce n))
                              (stop (After n)) | n | T}
                    ∪ {stop Exit}))
          (λs. ∃n. s = After n)
End

(*
 * defining the consumer
 *)

Definition prod_extract[simp]:
  prod_extract (Produce n) = n
End

Definition csm_tree_def:
  csm_tree = itree_iter (λ_. Vis Recv
                                 (λa. Vis (Send (prod_extract a))
                                          (λ_. Ret (INL ()))))
                        ()
End

Datatype:
  csm_states = Receiving | Sending
End

Definition csm_def:
  csm = fix ({ (Receiving,SOME(Recv,Produce n),Sending) | n | T }
           ∪ { (Sending, SOME(Send n,x),Receiving) | n,x | T }, Receiving)
            (λs. s = Sending)
End

(*
 * final linear correctness property
 *)

Definition prod_csm_com:
  prod_csm_com = { SOME (Recv,Produce n) | n < 256 }
End

Definition spec_def:
  spec = comm prod_csm_com prod csm
End

(* consider all completed, weakly fair traces *)

Type path[pp] = “:'s # ('a # 's) llist”;

CoInductive compl_trace:
  ((¬∃s'. (s,a,s') ∈ r) ⇒ compl_trace r (s,[||])) ∧
  ((s,a,s') ∈ r ∧ compl_trace r (s',p')
   ⇒ compl_trace r (s,(a,s'):::p'))
End

Definition nowlike:
  nowlike f (s,(a,_):::l) = ∃x. a = f x
End

CoInductive globally:
  (P (s,[||]) ⇒ globally P (s,[||])) ∧
  (P (s,(a,_):::p) ∧ globally P (s',p) ⇒ globally P (s,(a,s'):::p))
End

Inductive future:
  (P p' ⇒ future P p') ∧
  (future P (s',p) ⇒ future P (s,(a,s'):::p))
End

(* if s can always take transition a but does not necessarily take it *)
Definition perp_enabled:
  perp_enabled fairtr = globally (λp. case p of
                                        (s,(b,_):::p') => (∃a s'. (s,a,s') ∈ fairtr)
                                      | _ => F)
End

(* then one of the ‘fairtr’ transitions occurs *)
Definition tr_occurs:
  tr_occurs fairtr p = ∃s a s'. (s,a,s') ∈ fairtr ∧
                                future (λp. ∃p'. p = (s,(a,s'):::p')) p
End

Definition wfair:
  wfair fairtr = globally (λp. perp_enabled fairtr p ⇒ tr_occurs fairtr p)
End

Theorem progress_wfair_T:
  compl_trace r p ⇒ wfair r p
Proof
  rw[wfair] >>
  irule globally_coind >>
  qexists_tac ‘compl_trace r’ >>
  conj_tac >- (metis_tac[]) >>
  pop_assum kall_tac >>
  rw[] >>
  Cases_on ‘a0’ >> Cases_on ‘r'’ >-
   (fs[Once compl_trace_cases] >>
    rw[perp_enabled, Once globally_cases]) >>
  Cases_on ‘h’ >> rw[] >>
  qexists_tac ‘r'’ >>
  fs[Once compl_trace_cases] >>
  reverse (rw[tr_occurs]) >>
  rw[Once future_cases] >> metis_tac[]
QED

Definition fairtraces:
  fairtraces (r,i) P =
  (∀path. compl_trace r path ∧ FST path = i ∧ (∀t. t ∈ r ⇒ wfair {t} path) ⇒ P path)
End

Definition labels_def:
  labels (s,l) = LUNFOLD (λl. case l of
                                ((a,_):::l') => SOME (l',a)
                              | [||] => NONE) l
End

Theorem labels_thm:
  labels (s,[||]) = [||] ∧
  labels (s,(a,s'):::l) = a:::(labels (ARB,l))
Proof
  rw[labels_def] >> rw[Once LUNFOLD]
QED

(* transporting across the weak bisimulation *)

Inductive strip_NONE:
  strip_NONE (SOME x:::l) (SOME x:::l) ∧
  strip_NONE [||] [||] ∧
  (strip_NONE l l' ⇒ strip_NONE (NONE:::l) l')
End

CoInductive llist_wbisim:
  (llist_wbisim l l' ⇒ llist_wbisim (NONE:::l) (NONE:::l')) ∧
  (strip_NONE t [||] ∧ strip_NONE t' [||] ⇒
  llist_wbisim t t') ∧
  (llist_wbisim l l' ∧ strip_NONE xl (SOME x:::l) ∧ strip_NONE xl' (SOME x:::l') ⇒
  llist_wbisim xl xl')
End

Theorem strip_NONE_NONE[simp]:
  ∀l l'. strip_NONE (NONE:::l) l' <=> strip_NONE l l'
Proof
  rw[EQ_IMP_THM]
  >- last_x_assum $ strip_assume_tac o SRULE[Once strip_NONE_cases] >>
  metis_tac[strip_NONE_rules]
QED

Theorem llist_wbisim_refl:
  llist_wbisim l l
Proof
  irule llist_wbisim_coind >>
  qexists_tac ‘$=’ >>
  rw[] >>
  Cases_on ‘a0’ >> rw[] >-
   (metis_tac[strip_NONE_cases]) >>
  Cases_on ‘h’ >> metis_tac[strip_NONE_cases]
QED

Theorem llist_wbisim_sym:
  ∀l' l. llist_wbisim l l' ⇒ llist_wbisim l' l
Proof
  rw[] >>
  irule llist_wbisim_coind >>
  qexists_tac ‘λa b. ∃l1 l2. a = l1 ∧ b = l2 ∧ llist_wbisim l2 l1’ >>
  rw[] >> pop_last_assum kall_tac >>
  metis_tac[llist_wbisim_cases]
QED

Theorem llist_wbisim_upto:
  ∀R.
  (∀a0 a1.
    R a0 a1 ⇒
    (∃l l'. a0 = NONE:::l ∧ a1 = NONE:::l' ∧ (R l l' ∨ llist_wbisim l l')) ∨
    strip_NONE a0 [||] ∧ strip_NONE a1 [||] ∨
    ∃l l' x. (R l l' ∨ llist_wbisim l l')
    ∧ strip_NONE a0 (SOME x:::l) ∧ strip_NONE a1 (SOME x:::l')) ⇒
  ∀a0 a1. R a0 a1 ⇒ llist_wbisim a0 a1
Proof
  rw[] >>
  irule llist_wbisim_coind >>
  qexists_tac ‘λa b. R a b ∨ llist_wbisim a b’ >>
  rw[] >- metis_tac[] >>
  pop_last_assum kall_tac >> pop_last_assum kall_tac >>
  metis_tac[llist_wbisim_cases]
QED

Theorem llist_wbisim_NONE_eq:
  llist_wbisim (NONE:::l) l
Proof
  rw[] >>
  irule llist_wbisim_upto >>
  qexists_tac ‘λa b. ∃l. a = (NONE:::l) ∧ b = l’ >>
  rw[] >>
  Cases_on ‘a1’ >> rw[Once strip_NONE_cases] >>
  Cases_on ‘h’ >> rw[Once strip_NONE_cases] >>
  metis_tac[strip_NONE_cases, llist_wbisim_refl]
QED

Theorem IMP_llist_wbisim_NONE:
  llist_wbisim l l' ⇒ llist_wbisim l (NONE:::l')
Proof
  rw[] >>
  irule llist_wbisim_upto >>
  qexists_tac ‘λa b. ∃l1 l2. a = l1 ∧ b = (NONE:::l2) ∧ llist_wbisim l1 l2’ >>
  rw[] >> pop_last_assum kall_tac >>
  metis_tac[llist_wbisim_cases]
QED

Theorem llist_wbisim_NONE:
  (∀(l:'a option llist) l'. llist_wbisim (NONE:::l) l' <=> llist_wbisim l l') ∧
  (∀(l:'a option llist) l'. llist_wbisim l (NONE:::l') <=> llist_wbisim l l')
Proof
  conj_asm1_tac >-
   (rw[EQ_IMP_THM] >-
     (last_x_assum $ strip_assume_tac o SRULE[Once llist_wbisim_cases] >-
       metis_tac[IMP_llist_wbisim_NONE] >>
      metis_tac[llist_wbisim_rules,strip_NONE_NONE]) >>
    metis_tac[IMP_llist_wbisim_NONE,llist_wbisim_sym]) >>
  metis_tac[llist_wbisim_sym]
QED

Theorem strip_NONE_unique:
  ∀l l' l''. strip_NONE l l' ∧ strip_NONE l l'' ⇒ l' = l''
Proof
  cheat
QED

Theorem llist_wbisim_strip_NONE_nil:
  ∀t t'. llist_wbisim t t' ∧ strip_NONE t [||] ⇒ strip_NONE t' [||]
Proof
  cheat
QED

Theorem llist_wbisim_strip_NONE_cons_SOME:
  ∀t t'. llist_wbisim t t' ∧ strip_NONE t (SOME h:::l) ⇒
  ∃l'. strip_NONE t' (SOME h:::l') ∧ llist_wbisim l l'
Proof
  cheat
QED

Theorem llist_wbisim_SOME_strip_NONE:
  llist_wbisim l (SOME x:::xs) ⇒
  ∃ls. strip_NONE l (SOME x:::ls) ∧ llist_wbisim xs ls
Proof
  metis_tac[llist_wbisim_strip_NONE_cons_SOME, strip_NONE_cases, llist_wbisim_sym]
QED

Theorem llist_wbisim_trans:
  llist_wbisim l l' ∧ llist_wbisim l' l'' ⇒ llist_wbisim l l''
Proof
  rw[] >>
  irule llist_wbisim_coind >>
  qexists_tac ‘λa b. ∃l1 l2 l3. a = l1 ∧ b = l3
                                ∧ llist_wbisim l1 l2 ∧ llist_wbisim l2 l3’ >>
  reverse (rw[]) >- (metis_tac[]) >>
  pop_last_assum kall_tac >> pop_last_assum kall_tac >>
  Cases_on ‘a0’ >> Cases_on ‘a1’ >> gvs[] >-
   (metis_tac[llist_wbisim_cases, strip_NONE_cases]) >-
   (disj1_tac >> metis_tac[strip_NONE_cases, llist_wbisim_strip_NONE_nil]) >-
   (disj1_tac >> metis_tac[strip_NONE_cases, llist_wbisim_strip_NONE_nil,
                           llist_wbisim_sym]) >>
  Cases_on ‘h’ >> Cases_on ‘h'’ >> fs[llist_wbisim_NONE] >-
   (metis_tac[])
  >-
   (disj2_tac >>
    ‘∃l'. strip_NONE l2 (SOME x:::l') ∧ llist_wbisim t' l' ∧
          ∃l''. strip_NONE t (SOME x:::l'') ∧ llist_wbisim l' l''’
      by metis_tac[llist_wbisim_strip_NONE_cons_SOME, strip_NONE_cases,
                   llist_wbisim_sym] >>
    qexistsl_tac [‘l''’,‘t'’,‘x’] >> metis_tac[strip_NONE_cases, llist_wbisim_sym])
  >-
   (disj2_tac >>
    ‘∃l'. strip_NONE l2 (SOME x:::l') ∧ llist_wbisim t l' ∧
          ∃l''. strip_NONE t' (SOME x:::l'') ∧ llist_wbisim l' l''’
      by metis_tac[llist_wbisim_strip_NONE_cons_SOME, strip_NONE_cases] >>
    metis_tac[strip_NONE_cases])
  >-
   (disj2_tac >>
    ‘(∃l'. strip_NONE l2 (SOME x:::l') ∧ llist_wbisim t l') ∧
     ∃l''. strip_NONE l2 (SOME x':::l'') ∧ llist_wbisim t' l''’
      by metis_tac[llist_wbisim_SOME_strip_NONE, llist_wbisim_sym] >>
    ‘(SOME x:::l') = (SOME x':::l'')’ by metis_tac[strip_NONE_unique] >> gvs[] >>
    metis_tac[strip_NONE_cases, llist_wbisim_sym])
QED

(* any predicate respects weak trace equivalence is carried by wbisim *)
Theorem trace_transport:
  (∀la lb. llist_wbisim (labels la) (labels lb) ⇒ P la = P lb)
  ∧ lts_wbisim r r' i i'
  ∧ fairtraces (r',i') P
  ⇒ fairtraces (r,i) P
Proof
  rw[fairtraces] >>
  ‘∃(path' : (β option, α) path).
     FST path' = i' ∧ llist_wbisim (labels path) (labels path')’ by cheat >>
  last_x_assum drule >> rw[] >>
  pop_assum kall_tac >>
  last_x_assum irule >>
  rw[] >-
   (cheat
   ) >>
  irule compl_trace_coind >>
  cheat
QED

(* should really use a model checker here *)

Definition correctness:
  correctness = (globally
                 (λl. ∀n. nowlike (λ(_:unit). SOME(Recv,Produce n)) l
                          ⇒ future (nowlike (λx. SOME(Send n,x))) l))
End

Theorem correctness_resp:
  llist_wbisim (labels la) (labels lb) ⇒ correctness la = correctness lb
Proof
  cheat
QED

Theorem spec_property:
  fairtraces spec correctness
Proof
  cheat
QED

Theorem impl_has_spec_property:
  lts_wbisim (r :(prod_states # csm_states)
                 # (testev # testev) option # prod_states # csm_states -> bool)
  (lts_rel spec) i (lts_init spec)
  ⇒ fairtraces (r,i) correctness
Proof
  strip_tac >>
  irule trace_transport >>
  conj_tac >- (rw[correctness_resp]) >>
  qexistsl_tac [‘lts_init spec’, ‘lts_rel spec’] >>
  Cases_on ‘spec’ >>
  gvs[lts_rel, lts_init, spec_property]
QED






(* Theorem test: *)
(*   (∀x y. V(i(x,i(y,x)))) ∧ *)
(*   (∀x y z. V(i(i(x,i(y,z)), i(i(x,y),i(x,z))))) ∧ *)
(*   (* (∀x y. V(i(i(y,x),i(n(x),n(y))))) ∧ *) *)
(*   (∀x y. V(i(x,y)) ∧ V(x) ⇒ V(y)) *)
(*   ⇒ *)
(*   V(i(a,i(i(a,b),b))) *)
(* Proof *)
(*   metis_tac[] *)
(* QED *)

(* (* parallel compose itrees *)
(*  * separate type of completed communications *)
(*  * the presence of true nondet is messy *)
(*  *) *)

(* Datatype: *)
(*   message = Comm 'a 'a | Call 'a | Select | Choice num *)
(* End *)

(* Definition call_def: *)
(*   call (Call a) = a *)
(* End *)

(* Definition is_com_def: *)
(*   is_com com (Call e) (Call e') = com e e' ∧ *)
(*   is_com _ _ _ = F *)
(* End *)

(* Type comtree[pp] = “:(α message, α message, β option) itree”; *)

(* Definition select3_def: *)
(*   select3 t t' t'' = Vis Select *)
(*                          (λcb. case cb of *)
(*                                  Choice n => if n = 0 then t *)
(*                                              else if n = 1 then t' *)
(*                                              else if n = 2 then t'' *)
(*                                              else Ret (INR NONE) *)
(*                                | _ => ARB) *)
(* End *)

(* Definition par: *)
(*   par com (t : ('x,'y) comtree) (t' : ('x,'y) comtree) = *)
(*   iter *)
(*   (λseed. *)
(*      case seed of *)
(*        (Ret NONE, t) => Ret (INR NONE) *)
(*      | (t, Ret NONE) => Ret (INR NONE) *)
(*      | (Ret (SOME r), Ret (SOME r')) => Ret (INR (SOME (r, r'))) *)
(*      | (Tau t, Tau t') => Ret (INL (t, t')) *)
(*      | (Ret r, Tau t) => Ret (INL (Ret r, t)) *)
(*      | (Tau t, Ret r) => Ret (INL (t, Ret r)) *)
(*      | (Vis e k, Ret r) => Vis (Call (call e)) (λa. Ret (INL (k a, Ret r))) *)
(*      | (Ret r, Vis e k) => Vis (Call (call e)) (λa. Ret (INL (Ret r, k a))) *)
(*      | (Vis e k, Tau t) => (select3 *)
(*                             (Vis (Call (call e)) (λa. Ret (INL (k a, t)))) *)
(*                             (Ret (INL (Vis e k, t))) *)
(*                             (Ret (INR NONE))) *)
(*      | (Tau t, Vis e k) => (select3 *)
(*                             (Ret (INL (t, Vis e k))) *)
(*                             (Vis (Call (call e)) (λa. Ret (INL (t, k a)))) *)
(*                             (Ret (INR NONE))) *)
(*      (* maybe synchronize, while remaining open to other processes (can restrict) *) *)
(*      (* natmaps - quotient by branching *) *)
(*      | (Vis e k, Vis e' k') *)
(*        => if is_com com e e' *)
(*           then (select3 *)
(*                 (Vis (Comm (call e) (call e')) (λ_. Ret (INL (k e', k' e)))) *)
(*                 (Vis (Call (call e)) (λa. Ret (INL (k a, Vis e' k')))) *)
(*                 (Vis (Call (call e')) (λa. Ret (INL (Vis e k, k' a))))) *)
(*           else (select3 *)
(*                 (Vis (Call (call e)) (λa. Ret (INL (k a, Vis e' k')))) *)
(*                 (Vis (Call (call e')) (λa. Ret (INL (Vis e k, k' a)))) *)
(*                 (Ret (INR NONE))) *)
(*   ) (t,t') *)
(* End *)

Definition itree_trigger_def:
  itree_trigger event = Vis event Ret
End

(* these are useful ONLY for bisimulation *)
val or1_tac = disj1_tac
val or2_tac = disj2_tac >> disj1_tac;
val or3_tac = disj2_tac >> disj2_tac;

(*/ basic examples of itree definition
   itree_unfold f is the final (coinductive) arrow to the final coalgebra
   where f = structure map (into primed itree), status = itree algebra instance
 *)

(* echo taken from paper, a bit different with HOL unfold vs deptypes *)
(* note: Vis (e : E) (A e -> Itree E A R) is not the same, as we cannot distinguish
         the intended response for a given event data e.g. nat for file desc/output *)
Datatype:
  IO = Input | Output num
End

Definition echo:
  echo = itree_unfold (λ s. case s of
                            | Input    => Vis' Input      (λ n. Output n)
                            | Output n => Vis' (Output n) (λ v. Input))
                      Input
End

Theorem echo_unfold:
  echo = Vis Input (λ n. Vis (Output n) (λ_. echo))
Proof
  rw[echo,       Once itree_unfold] >>
  rw[FUN_EQ_THM, Once itree_unfold]
QED

(* simple stuff *)

Theorem itree_bind_emit:
  (emit e) >>= k = Vis e k
Proof
  rw[itree_trigger_def, itree_bind_thm, FUN_EQ_THM]
QED

Theorem itree_bind_tau_inv:
  t >>= k = Tau s ∧ (¬∃r. t = Ret r) ⇒ ∃s'. t = Tau s' ∧ s' >>= k = s
Proof
  Cases_on ‘t’ >> fs[itree_bind_thm]
QED

Theorem itree_bind_vis_inv:
  t >>= cont = Vis e k ∧ (¬∃r. t = Ret r)
  ⇒ ∃k'. t = Vis e k' ∧ ∀x. (k' x) >>= cont = k x
Proof
  Cases_on ‘t’ >> fs[itree_bind_thm] >>
  rw[FUN_EQ_THM]
QED

Theorem itree_wbisim_vis:
  ∀e k1 k2. (∀r. k1 r ≈ k2 r) ⇒ Vis e k1 ≈ Vis e k2
Proof
  metis_tac[strip_tau_cases, itree_wbisim_cases]
QED

val vis_tac = irule itree_wbisim_vis >> Cases;

(* finite on all paths: generates backwards coind & forwards cases *)
CoInductive itree_fin:
  (∀t. itree_fin t ⇒ itree_fin (Tau t)) ∧
  (∀e k. (∀r. itree_fin (k r)) ⇒ itree_fin (Vis e k)) ∧
  (∀r. itree_fin (Ret r))
End

(* infinite on all paths *)
CoInductive itree_inf:
  (∀t. itree_inf t ⇒ itree_inf (Tau t)) ∧
  (∀e k. (∀r. itree_inf (k r)) ⇒ itree_inf (Vis e k))
End

Theorem ret_fin:
  itree_fin (Tau (Ret r))
Proof
  rw[Once itree_fin_cases] >>
  rw[Once itree_fin_cases]
QED

Definition vis_spin_def:
  vis_spin = itree_unfold (λs. Vis' s I) 0
End

Theorem vis_spin_inf:
  itree_inf vis_spin
Proof
  irule itree_inf_coind >>
  qexists_tac ‘λt. ∃k. t = Vis k (itree_unfold (λs. Vis' s I))’ >>
  rw[vis_spin_def] >>
  rw[Once itree_unfold]
QED

(* looping vis nodes *)

Definition iterate_def:
  iterate emit succ zero =
  itree_unfold (λs'. Vis' (emit s') (λ_. (succ s'))) zero
End

(*/ recursive specifications
   testing
 *)

open arithmeticTheory;

Definition even_spec_def:
  even_spec k = iterate (λx. if EVEN x then "even" else "odd") (λn. 1 + n) k
End

Theorem even_add1:
  EVEN k ⇔ ¬EVEN (k+1)
Proof
  metis_tac[EVEN, SUC_ONE_ADD, ADD_SYM]
QED

(* backwards extensionality *)
Theorem even_spec_unfold:
  ∀k. EVEN k ⇒ even_spec k = Vis "even" (λ_. Vis "odd" (λ_. even_spec (2 + k)))
Proof
  rw[even_spec_def] >>
  CONV_TAC $ LHS_CONV $ REWRITE_CONV[iterate_def] >>
  rw[itree_unfold] >>
  rw[combinTheory.o_DEF] >>
  rw[FUN_EQ_THM] >>
  rw[itree_unfold] >-
   (metis_tac[even_add1]) >-
   (rw[combinTheory.o_DEF] >>
    rw[iterate_def])
QED

Theorem even_add2:
  EVEN (n+2) ⇔ EVEN n
Proof
  rw[EVEN_ADD]
QED

Theorem even_spec_plus2:
  ∀k. even_spec (2+k) = even_spec k
Proof
  strip_tac >>
  qspecl_then [‘even_spec (2+k)’, ‘even_spec k’]
              strip_assume_tac itree_bisimulation >>
  fs[EQ_IMP_THM] >>
  pop_assum irule >>
  pop_assum kall_tac >>
  qexists_tac ‘λa b. ∃n. a = even_spec (2+n) ∧ b = even_spec n’ >>
  rw[] >> gvs[even_spec_def, iterate_def, Once itree_unfold] >-
   (qexists_tac ‘k’ >>
    simp[] >>
    CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV[itree_unfold] >>
    rw[]) >-
   (simp[Once itree_unfold] >>
    CONJ_TAC >-
     (rw[Once even_add2]) >-
     (qexists_tac ‘n+1’ >> rw[]))
QED

Theorem even_spec_thm:
  even_spec 0 = (emit "even" >>= (λ_. (emit "odd")))
              >>= (λ_. even_spec 0)
Proof
  rw[Once even_spec_unfold] >>
  rw[itree_bind_emit] >>
  rw[itree_bind_thm] >>
  rw[FUN_EQ_THM] >>
  rw[itree_bind_emit] >>
  rw[FUN_EQ_THM] >>
  qspec_then ‘0’ mp_tac even_spec_plus2 >>
  rw[]
QED
