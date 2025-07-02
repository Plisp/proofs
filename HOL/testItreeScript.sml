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

open stringLib; (* parsing, text examples etc. *)
open itreeTauTheory;

open relationTheory bisimulationTheory;
open pathTheory;

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
 * state predicate, transition relation, initial state, success predicate
 *)
Type lts[pp] = “:((α -> bool) # (α # β option # α -> bool) # α)”;

Definition lts_states[simp]:
  lts_states ((c,r,i) : ('s,'a) lts) = c
End
Definition lts_rel[simp]:
  lts_rel ((c,r,i) : ('s,'a) lts) = r
End
Definition lts_init[simp]:
  lts_init ((c,r,i) : ('s,'a) lts) = i
End

Definition curry3[simp]:
  curry3 P = λa b c. P (a,b,c)
End
Definition uncurry3[simp]:
  uncurry3 Q = λ(a,b,c). Q a b c
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

Definition comm_rel_com:
  comm_rel_com com r r' = { ((s,t), a, (s',t')) | a ∉ com ∧ (t,a,t') ∈ r'∧ s = s' }
End

Definition comm_rel:
  comm_rel com r r' = comm_rel_l com r ∪ comm_rel_r com r' ∪ comm_rel_com com r r'
End

Definition comm:
  comm com ((c,r,i) : ('s,'a) lts) ((c',r',i') : ('t,'a) lts) =
  ({ (s,s') | c s ∧ c' s'}, comm_rel com r r', (i,i'))
End

Definition par:
  par l1 l2 = comm ∅ l1 l2
End

Definition prefix:
  prefix i' a ((c,r,i) : ('s,'a) lts) = (c ∪ {i'}, r ∪ {(i',a,i)},i')
End

(* this is more natural than restriction *)
Definition hide:
  hide ((c,r,i) : ('s,'a) lts) a =
  (c,{ (s,NONE,s') | (s,a,s') ∈ r } ∪ { (s,a',s') | a' ≠ a ∧ (s,a',s') ∈ r }, i)
End

Definition choice_ext:
  choice_ext s a ((c,r,i) : ('s,'a) lts) a' ((c',r',i') : ('s,'a) lts) =
  ({s} ∪ c ∪ c', r ∪ { (s,a,i); (s,a',i') }, s)
End

Definition choice_int:
  choice_int s l1 l2 = choice_ext s NONE l1 NONE l2
End

(* monad *)
Definition seq:
  seq ((c,r,i) : ('s,'a) lts) (final : 's -> bool) (next : 's -> ('s,'a) lts) =
  (c ∪ BIGUNION { lts_states (next s) | final s },
   r ∪ { (fs,NONE,lts_init (next fs)) | final fs }
     ∪ BIGUNION { lts_rel (next s) | final s },
   i)
End

Definition fix:
  fix ((c,r,i) : ('s,'a) lts) (final : 's -> bool)
  = seq (c,r,i) final (K (c,r,i))
End

(* the equivalence of choice: weak bisimulation, a congruence for csp
 * more fine than trace equivalence for dealing with liveness
 *)

Definition curry3[simp]:
  curry3 r = (λs a s'. (s,a,s') ∈ r)
End

Definition lts_wbisim:
  lts_wbisim r s t = WBISIM_REL (curry3 r) NONE s t
End

(* XXX can't enable types *)
Theorem lts_wbisim_refl[simp]:
  lts_wbisim r s s
Proof
  rw[lts_wbisim] >>
  metis_tac[WBISIM_REL_IS_EQUIV_REL, equivalence_def, reflexive_def]
QED

Theorem lts_wbisim_sym:
  lts_wbisim r s t ⇒ lts_wbisim r t s
Proof
  rw[lts_wbisim] >>
  metis_tac[WBISIM_REL_IS_EQUIV_REL, equivalence_def, symmetric_def]
QED

Theorem lts_wbisim_trans:
  lts_wbisim r s t ∧ lts_wbisim r t u ⇒ lts_wbisim r s u
Proof
  rw[lts_wbisim] >>
  metis_tac[WBISIM_REL_IS_EQUIV_REL, equivalence_def, transitive_def]
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

(* lts predicates *)

CoInductive lts_globally:
  (∀s' a. (s,a,s') ∈ r ⇒ P (s,a,s') ∧ lts_globally r P s')
  ⇒ lts_globally r P s
End

Inductive lts_future:
  (∀s a. (s,a,s') ∈ r ⇒ P (s,a,s') ∨ lts_future r P s')
  ⇒ lts_future r P s
End

(* TODO preservation under weak bisimulation
 * TODO syntax for transitions s -r-> s' and weak bisimilarity s ≈r≈ s
 * P must respect weakly bisimilar states
 *)

Theorem globally_resp_wbisim:
  lts_wbisim (r ∪ r') s s' ∧ (∀s s'. P (s,NONE,s'))
  ⇒ lts_globally r P s ⇒ lts_globally r' P s'
Proof
  cheat
QED

(* the producer produces buffers (represented as numbers / pointers)
 * and can sometimes stop in the false state.
 * Meanwhile the consumer receives and sends them
 *)

Datatype:
  testev = Produce num | Recv | Send num
End

Definition prod_def:
  prod = (K T, { (T,SOME(Recv,Produce n),T) | n < 256 } ∪ {(T,NONE,F)}, T)
         : (bool, testev # testev) lts
End

(* sanity check: we can continuously produce the 0 pointer *)
Theorem test_okpath:
  okpath (curry3 (lts_rel prod))
         (unfold (λ_. T) (λ_. SOME ((),SOME (Recv,Produce 0))) ())
Proof
  irule okpath_unfold >>
  qexists_tac ‘K T’ >>
  rw[prod_def]
QED

Definition prod_extract[simp]:
  prod_extract (Produce n) = n
End

Definition csm_tree_def:
  csm_tree = itree_iter (λ_. Vis Recv
                                 (λa. Vis (Send (prod_extract a))
                                          (λ_. Ret (INL ()))))
                        ()
End

(* FINAL linear correctness statement *)
Definition prod_csm_com:
  prod_csm_com = { SOME (Recv,Produce n) | n < 256 }
End

Definition sys_def[simp]:
  sys = comm prod_csm_com prod (itree_sm csm_tree)
End

Theorem comm_rel_r_lift:
  ((s,t),a,(s',t')) ∈ comm_rel_r com r' ⇔ a ∉ com ∧ (t,a,t') ∈ r' ∧ s = s'
Proof
  rw[comm_rel_r] >> metis_tac[]
QED

Theorem correspondence:
  lts_wbisim (comm_rel com r r')
Proof
QED

(* XXX types are wrong *)
Theorem correctness:
  lts_globally sys
  (λ(s,a,s'). prod_csm_com a
              ⇒ (lts_future sys (λ(s,a,s'). ∃x. a = SOME (Send n,x)) s'))
  (lts_init sys)
Proof
QED

(* TODO can extend to statement about traces *)

Definition allpaths:
  allpaths lts P = (∀path. okpath (curry3 (lts_rel lts)) path ⇒ P path)
End

Definition nowlike:
  nowlike f p = ∃x. first_label p = f x
End

CoInductive globally:
  (P (pcons s a p) ∧ globally P p) ⇒ globally P (pcons s a p)
End

Inductive future:
  (∀P p. P p ⇒ future P p) ∧
  (∀s a P p. future P p ⇒ future P (pcons s a p))
End







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
