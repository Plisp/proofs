open bossLib whileTheory pred_setTheory relationTheory optionTheory;
open arithmeticTheory numLib BasicProvers dep_rewrite;
open listTheory llistTheory;

(* This tutorial should be easy to read to get the vibe of coinduction:
* https://paulhe.com/2019/04/17/coinduction.html *)

(* 3 ways to think about Inductive sets.
* 1. the least fixed point such that X=F(X)
* 2. the smallest set that is closed forward (F(X) ⊆ X) (by Knaster-Tarski Thm)
* 3. the limit of keep applying F to {} (by Kleene fixed point thm)
* (keep adding elements to {} until it is closed) *)

Inductive even_list:
  even_list [] ∧
  (∀x xs. EVEN x ∧ even_list xs ⇒ even_list (x::xs))
End

CoInductive inf:
  inf l ⇒ inf (e:::l)
End

Theorem test:
  inf l ⇒ ¬(LFINITE l)
Proof
  spose_not_then assume_tac >>
  pop_assum mp_tac >>
  qid_spec_tac ‘l’ >>
  Induct_on ‘LFINITE l’ >>
  gvs[Once inf_cases] >>
  rw[] >>
  pop_last_assum kall_tac >>
  rw[Once inf_cases] >>
QED

(* F(X) = {[]} ∪ {y | y = x:: xs ∧ EVEN x ∧ xs ∈ X} *)
(* F(X) ⊆ X = {[]} ∪ {y | y = x:: xs ∧ EVEN x ∧ xs ∈ X} ⊆ X *)
(* = [] ∈ X ∧ (!y x xs. y = x::xs ∧ EVEN x ∧ xs ∈ X ⇒ y ∈ X *)
(* X ⊆ F(X) = X ⊆ ({[]} ∪ {x | x = y::ys ∧ EVEN y ∧ ys ∈ X}) *)
(* = ∀x. x ∈ X  ⇒ x = [] ∨ ∃y ys. x = y::ys ∧ EVEN y ∧ ys ∈ X *)

(* The smallest set S that satifies F(S) ⊆ S *)
(* ∀X. F(X) ⊆ X ⇒ S ⊆ X *) (* This is the induction principle *)
(* ∀X. ([] ∈ X ∧ (!y x xs. y = x::xs ∧ EVEN x ∧ xs ∈ X ⇒ y ∈ X) ⇒
* (∀x. x ∈ S ⇒ x ∈ X) *)

Theorem even_list_empty = cj 1 even_list_rules;
Theorem even_list_cons = cj 2 even_list_rules;

Theorem even_list_example:
  even_list [0;2;4;6;8]
Proof
  rpt $ irule_at Any even_list_cons >>
  simp[] >>
  irule even_list_empty
QED

(* lets use llist (coinductiv/lazy list) instead *)
Inductive even_llist:
  even_llist [||] (* empty llist *) ∧
  (∀x xs. EVEN x ∧ even_llist xs ⇒ even_llist (x:::xs))
  (* ::: is the cons for llist *)
End

(* should be similar to even_list as the predicate is essentially the same *)
Theorem even_llist_example:
  even_llist [|0;2;4;6;8|]
Proof
  rpt (irule (cj 2 even_llist_rules) >> rw[]) >>
  irule (cj 1 even_llist_rules)
QED

(* LUNFOLD is a way to create corecursive function.
* It is essentially unfold in Haskell.
* The second argument can be treated as the initial state.
* The first argument is applied on the initial state and
* return the next state, and the head of the list.
* We keep applying the function until we gets to NONE.
* This allows the list to be infinite as the function
* may never return NONE *)
LUNFOLD;

Definition twos_def:
  twos = LUNFOLD (λu. SOME ((),2)) ()
End

Theorem twos:
  2:::twos = twos
Proof
  simp[twos_def] >>
  irule EQ_SYM >>
  simp[Once LUNFOLD]
QED

(* Try to prove this first *)
(* Theorem even_llist_twos: *)
(*   even_llist twos *)
(* Proof *)
(* QED *)
(* It turns out that you cannot prove it. Why? *)

(* In fact, we can use induction to prove that `twos`
 * is not a even_llist *)
Theorem not_even_llist_twos:
  ¬even_llist twos
Proof
  ‘even_llist twos ⇒ (λl. ∀x. x:::l ≠ l) twos’ suffices_by metis_tac[twos] >>
  strip_tac >>
  irule even_llist_ind >>
  rw[]
QED

(* so how should define even_llist? *)
CoInductive even_llist:
  even_llist [||] ∧
  (∀x xs. EVEN x ∧ even_llist xs ⇒ even_llist (x:::xs))
End

(* What theorems does this gives you?
* How is this different from the inductive version? *)

(* 3 ways to think about CoInductive sets.
* 1. the greatest fixed point such that X=F(X)
* 2. the largest set that is closed backward (X ⊆ F(X)) (by Knaster-Tarski Thm)
* 3. keep removing elements that does not satisfy the rule from UNIV
* until it is closed *)

(* The largest set S that satifies S ⊆ F(S) *)
(* ∀X. X ⊆ F(X) ⇒ X ⊆ S *) (* This is the coinduction principle *)
(* ∀X. (∀x. x ∈ X ⇒ x = [||] ∨ ∃y ys. x = y:::ys ∧ EVEN y ∧ ys ∈ X) ⇒
* (∀x. x ∈ X ⇒ x ∈ S) *)
(* A coinductive proof is essentially finding an X such that
* the thing you are proving is in X such and
* ∀x. x ∈ X ⇒ x = [||] ∨ ∃y ys. x = y:::ys ∧ EVEN y ∧ ys ∈ X *)
Theorem even_llist_cons = cj 2 even_llist_rules;
Theorem even_llist_empty = cj 1 even_llist_rules;
Theorem even_llist_example:
  even_llist [|0;2;4;6;8|]
Proof
  rpt $ irule_at Any even_llist_cons >>
  simp[] >>
  irule even_llist_empty
QED


(* hint: use even_llist_coind *)
(* Which set that is closed-backward should we choose? *)
Theorem even_llist_twos:
  even_llist twos
Proof
  irule even_llist_coind >>
  qexists_tac ‘{ twos }’ >>
  rw[] >> disj2_tac >>
  qexists_tac ‘2’ >>
  rw[EVEN_ADD, twos]
QED

Definition inc2_def:
  inc2 n = LUNFOLD (λn. SOME (n+2,n)) n
End

Theorem inc2:
  n:::(inc2 $ n+2) = inc2 n
Proof
  rw[inc2_def] >>
  rw[SimpR “$=”, Once LUNFOLD]
QED

(* which set should we use? Is {inc2 0} closed-backward *)
Theorem even_llist_inc2:
  even_llist (inc2 0)
Proof
  irule even_llist_coind >>
  qexists_tac ‘{ inc2 n | EVEN n }’ >>
  rw[EVEN] >- metis_tac[EVEN] >>
  disj2_tac >>
  qexistsl_tac [‘n’, ‘(inc2 $ n+2)’] >>
  rw[inc2, EVEN] >>
  qexists_tac ‘n+2’ >> rw[] >>
  rw[EVEN, EVEN_ADD]
QED

(* This is essentially MEM, but in a predicate form *)
Inductive mem:
  (!x xs. mem x (x:::xs)) ∧
  (!x y xs. mem x xs ==> mem x (y:::xs))
End

(* What is the coinductive version of mem? *)
CoInductive comem:
  (!x xs. comem x (x:::xs)) ∧
  (!x y xs. comem x xs ==> comem x (y:::xs))
End

(* we get the coinduction principle:
* (x,ys) ∈ S ⇒
* (∃xs. ys = x:::xs) ∨
* (∃y xs. ys = y:::xs ∧ (x,xs) ∈ S) *)

(* what happend when the second argument is not finite *)
Theorem inf_imp_comem:
  !x l. ~(LFINITE l) ==> comem x l
Proof
  rw[] >>
  irule comem_coind >>
  qexists_tac ‘λa xs. ¬LFINITE xs’ >>
  rw[] >>
  pop_last_assum kall_tac >>
  Cases_on ‘a1’ >> fs[]
QED

CoInductive not_mem:
  (!x. not_mem x [||]) /\
  (!x y xs. not_mem x xs /\ y <> x ==> not_mem x (y:::xs))
End

Theorem not_mem_LNTH:
  not_mem x l <=> !n. LNTH n l <> SOME x
Proof
  rw[EQ_IMP_THM] >-
   (pop_assum mp_tac >>
    qid_spec_tac ‘l’ >>
    Induct_on ‘n’ >-
     (rw[] >> Cases_on ‘l’ >> fs[Once not_mem_cases]) >>
    strip_tac >>
    Cases_on ‘l’ >> rw[Once not_mem_cases]) >>
  irule not_mem_coind >>
  qexists_tac ‘λa as. (∀n. LNTH n as ≠ SOME a)’ >>
  rw[] >>
  Cases_on ‘a1’ >> fs[] >>
  reverse (rw[]) >-
   (pop_assum $ qspec_then ‘0’ strip_assume_tac >>
    fs[LNTH]) >>
  pop_assum $ qspec_then ‘SUC n’ strip_assume_tac >>
  gvs[LNTH_THM]
QED

(* Is this a coincidence that
* you can define the negation of inductive predicate
* as a coinductive predicate? *)
Theorem mem_not_mem:
  mem x l <=> ~(not_mem x l)
Proof
  ‘mem x l ⇔ (∃n. LNTH n l = SOME x)’ by cheat >>
  gvs[not_mem_LNTH]
QED

(* Prove this with coinduction *)
Theorem not_mem_inc2:
  ∀n. ¬EVEN n ⇒ not_mem n (inc2 0)
Proof
  rw[] >>
  irule not_mem_coind >>
  qexists_tac ‘λa b. ¬EVEN a ∧ b ∈ { inc2 n | EVEN n }’ >>
  reverse (rw[]) >-
   (metis_tac[EVEN,EVEN_ADD]) >>
  disj2_tac >>
  rw[Once $ GSYM inc2, EVEN, EVEN_ADD] >-
   (‘EVEN 2’ suffices_by metis_tac[EVEN,EVEN_ADD] >> rw[]) >>
  metis_tac[]
QED

(* Can you use induction to prove this using mem_not_mem? No? *)
(* Theorem not_mem_inc2: *)
(*   ∀n. ¬EVEN n ⇒ not_mem n (inc2 0) *)
(* Proof *)
(* QED *)

(* bisimilarity *)
(* Try to define odds such that
* theorem odds and odds_example are true *)
Definition odds_def:
  odds l = LUNFOLD (λs.
                      case s of
                        [|x|] => SOME ([||], x)
                      | x:::(x':::xs) => SOME (xs, x)
                      | _ => NONE)
                   l
End

Definition evens_def:
  evens l =
    case LTL l of
      | NONE => [||]
      | SOME tl => odds tl
End

Definition merge_def:
  merge l l' = LUNFOLD (λp.
    case p of
      | ([||],[||]) => NONE
      | ([||],x:::xs) => SOME (([||],xs),x)
      | (x:::xs,ys) => SOME ((ys,xs),x)) (l,l')
End

Theorem odds:
  (odds [||] = [||]) ∧
  (∀x. odds [|x|] = [|x|]) ∧
  (∀x y zs. odds (x:::y:::zs) = x:::odds zs)
Proof
  rw[odds_def] >> rw[Once LUNFOLD] >>
  rw[Once LUNFOLD]
QED

Theorem odds_example:
  odds [|1;2;3;4;5|] = [|1;3;5|] ∧
  odds [|0;1;2;3;4;5|] = [|0;2;4|]
Proof
  rpt (rw[odds_def, Once LUNFOLD])
QED

Theorem evens_to_odds:
  (evens [||] = [||]) ∧
  (∀x ys. evens (x:::ys) = odds ys)
Proof
  rw[evens_def]
QED

Theorem evens:
  (evens [||] = [||]) ∧
  (∀x. evens [|x|] = [||]) ∧
  (!x y zs. evens (x:::y:::zs) = y:::evens zs)
Proof
  simp[evens_to_odds,odds] >>
  Cases_on `zs` >>
  simp[evens_to_odds,odds]
QED

Theorem merge:
  (!(l:'a llist) t. merge [||] l = l) ∧
  (!(lh:'a) lt r. merge (lh:::lt) r = lh:::merge r lt)
Proof
  conj_asm1_tac
  >- (
    rw[Once LLIST_BISIMULATION] >>
    qexists `\m l. case l of
                   | [||] => m = [||]
                   | h:::t => m = merge [||] (h:::t)` >>
    rw[]
    >- (
      Cases_on `l` >>
      simp[merge_def,Once LUNFOLD]
    ) >>
    Cases_on `ll4` >>
    fs[] >>
    simp[merge_def,Once LUNFOLD] >>
    CASE_TAC >>
    simp[Once LUNFOLD]) >>
  rw[Once LLIST_BISIMULATION] >>
  qexists `\m m'.
    (?l l'. m = merge l l' ∧
      case l of
        | [||] => m' = l'
        | h:::t => m' = h:::merge l' t)` >>
  simp[] >>
  conj_tac
  >- (
    irule_at (Pos hd) EQ_REFL >>
    simp[]) >>
  rw[] >>
  Cases_on `l`
  >- (
    fs[] >>
    Cases_on `l'` >>
    fs[] >>
    qexistsl [`[||]`,`t`] >>
    simp[]) >>
  fs[] >>
  conj_tac >- simp[merge_def] >>
  qexistsl [`l'`,`t`] >>
  Cases_on`l'`>>
  fs[merge_def] >>
  simp[Once LUNFOLD]
QED

(* XXX funny lemma *)
Theorem odds_to_evens:
  (∀x ys. odds (x:::ys) = x ::: (evens ys))
Proof
  Cases_on ‘ys’ >> simp[odds, evens] >>
  rw[evens_to_odds]
QED

(* hint:
* You may use LLIST_BISIMULATION or
* LLIST_BISIMULATION0 *)
Theorem merge_odds_evens:
  merge (odds l) (evens l) = l
Proof
  rw[Once LLIST_BISIMULATION] >>
  qexists_tac ‘λa b. ∃x. a = (merge (odds x) (evens x)) ∧ b = x’ >>
  rw[] >>
  Cases_on ‘ll4’ >-
   (rw[odds, evens, merge]) >>
  Cases_on ‘t’ >> simp[odds, evens, merge] >>
  rw[evens_to_odds, odds_to_evens] >>
  rw[merge]
QED

(* LAPPEND is similarly to itree_bind *)
LAPPEND;
Theorem even_llist_coind_upto:
  ∀even_llist'.
  (∀a0.
    even_llist' a0 ⇒
    a0 = [||] ∨ ∃x xs. a0 = x:::xs ∧ EVEN x ∧ even_llist' xs ∨ even_llist a0) ⇒
  ∀a0. even_llist' a0 ⇒ even_llist a0
Proof
  rw[] >>
  irule even_llist_coind >>
  qexists_tac ‘λl. even_llist' l ∨ even_llist l’ >>
  rw[] >-
   (metis_tac[even_llist_cases]) >>
  (metis_tac[even_llist_cases])
QED

Theorem even_llist_LAPPEND_upto:
  even_llist l ∧ even_llist r ⇒ even_llist (LAPPEND l r)
Proof
  rw[] >>
  irule even_llist_coind_upto >>
  qexists_tac ‘λa. ∃l. (a = l ++ₗ r) ∧ even_llist l’ >>
  rw[] >-
   (metis_tac[]) >>
  pop_last_assum kall_tac >>
  (* XXX below proof doesn't work with fs! *)
  fs[Once even_llist_cases] >> metis_tac[even_llist_cases]
QED

Theorem even_llist_LAPPEND:
  even_llist l ∧ even_llist r ⇒ even_llist (LAPPEND l r)
Proof
  rw[] >>
  irule even_llist_coind >>
  qexists_tac ‘λa. ∃l. (a = l ++ₗ r ∨ a = l) ∧ even_llist l’ >>
  rw[] >-
   (metis_tac[]) >>
  pop_last_assum kall_tac >>
  pop_assum mp_tac >>
  rw[Once even_llist_cases] >> metis_tac[even_llist_cases]
QED

Theorem mem_LAPPEND:
  ∀x l. mem x l ⇒ mem x (LAPPEND l r)
Proof
  ho_match_mp_tac mem_ind >>
  rpt (rw[Once mem_rules])
QED






(* wbisim exercises *)
(* remove NONE finitely many times.
* Note that head on the left hand side cannot be NONE *)
Inductive strip_NONE:
  strip_NONE (SOME x:::l) (SOME x:::l) ∧
  strip_NONE [||] [||] ∧
  (strip_NONE l l' ⇒ strip_NONE (NONE:::l) l')
End

(* To make life easier. You can use
* ``Cases_on `blah` using optoin_list_CASES``
* to get all the three cases at once *)
Theorem option_list_CASES:
  ∀ol. (∃h l. ol = SOME h:::l) ∨ (∃l. ol = NONE:::l) ∨ ol = [||]
Proof
  gen_tac >>
  Cases_on `ol` >>
  simp[] >>
  Cases_on `h` >>
  simp[]
QED

(* weak bisimilar for llist *)
(* We can ignore finitely many taus. But if there
* are infinite taus, we want to keep it as it represents
* divergent process *)
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
  >- last_x_assum $ strip_assume_tac o
    SRULE[Once strip_NONE_cases] >>
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

Triviality test:
  ∀R.
  llist_wbisim a0 a1 ⇒
  (∃l l'. a0 = NONE:::l ∧ a1 = NONE:::l' ∧ (R l l' ∨ llist_wbisim l l')) ∨
  strip_NONE a0 [||] ∧ strip_NONE a1 [||] ∨
  ∃l l' x. (R l l' ∨ llist_wbisim l l')
           ∧ strip_NONE a0 (SOME x:::l) ∧ strip_NONE a1 (SOME x:::l')
Proof
  metis_tac[llist_wbisim_cases]
QED

Theorem llist_wbisim_upto_strong:
  ∀R.
  (∀a0 a1.
    R a0 a1 ⇒
    llist_wbisim a0 a1 ∨
    (∃l l'. a0 = NONE:::l ∧ a1 = NONE:::l' ∧ (R l l' ∨ llist_wbisim l l')) ∨
    strip_NONE a0 [||] ∧ strip_NONE a1 [||] ∨
    ∃l l' x. (R l l' ∨ llist_wbisim l l')
    ∧ strip_NONE a0 (SOME x:::l) ∧ strip_NONE a1 (SOME x:::l')) ⇒
  ∀a0 a1. R a0 a1 ⇒ llist_wbisim a0 a1
Proof
  rw[] >>
  irule llist_wbisim_upto >>
  qexists_tac ‘R’ >>
  metis_tac[test]
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

Theorem llist_wbisim_SOME_strip_NONE_sym:
  llist_wbisim (SOME x:::xs) l ⇒
  ∃ls. strip_NONE l (SOME x:::ls) ∧ llist_wbisim xs ls
Proof
  metis_tac[llist_wbisim_strip_NONE_cons_SOME, strip_NONE_cases, llist_wbisim_sym]
QED

(* There are quite a lot of cases in this proof *)
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






(* Theorem llist_wbisim_strip_NONE: *)
(*   !t t' t''. llist_wbisim t t' /\ strip_NONE t t'' ==> llist_wbisim t'' t' *)
(* Proof *)
(*   cheat *)
(* QED *)

(* Theorem llist_wbisim_strip_NONE_2: *)
(*   !t t' t''. llist_wbisim t t' /\ strip_NONE t' t'' ==> llist_wbisim t t'' *)
(* Proof *)
(*   metis_tac[llist_wbisim_strip_NONE, llist_wbisim_sym] *)
(* QED *)

Theorem strip_NONE_LAPPEND_SOME_strip_NONE:
  ∀a x l b. strip_NONE a (SOME x:::l) ⇒
    strip_NONE (LAPPEND a b) (SOME x ::: LAPPEND l b)
Proof
  cheat
QED

(* Theorem strip_NONE_LAPPEND_nil_strip_NONE: *)
(*   ∀a. strip_NONE a [||] ∧ strip_NONE b b' ⇒ *)
(*   strip_NONE (LAPPEND a b) b' *)
(* Proof *)
(*   cheat *)
(* QED *)

(* Theorem strip_NONE_nil_LAPPEND_NONE: *)
(*   ∀a l. strip_NONE a [||] ⇒ *)
(*     ∃l'. LAPPEND a (NONE:::l) = NONE:::l' ∧ *)
(*     llist_wbisim l' l *)
(* Proof *)
(*   cheat *)
(* QED *)

Theorem llist_strip_NONE_nil_wbisim:
  strip_NONE a [||] ⇒ llist_wbisim b (a ++ₗ b)
Proof
  Induct_on ‘strip_NONE’ >> rw[llist_wbisim_refl] >>
  rw[llist_wbisim_NONE]
QED

Theorem LAPPEND_llist_wbisim:
  llist_wbisim l l' ∧ llist_wbisim r r' ⇒
  llist_wbisim (LAPPEND l r) (LAPPEND l' r')
Proof
  rw[] >>
  irule llist_wbisim_upto_strong >>
  qexists_tac ‘λa b. ∃l1 l2 r1 r2. a = LAPPEND l1 r1 ∧ b = LAPPEND l2 r2
                                   ∧ llist_wbisim l1 l2 ∧ llist_wbisim r1 r2’ >>
  reverse(rw[]) >- metis_tac[] >>
  pop_last_assum kall_tac >> pop_last_assum kall_tac >>
  Cases_on ‘l1’ >> Cases_on ‘l2’ >> rw[] >-
   (disj1_tac >>
    ‘strip_NONE (h:::t) [||]’ by metis_tac[llist_wbisim_strip_NONE_nil,
                                           strip_NONE_cases] >>
    CONV_TAC $ RAND_CONV $ ONCE_REWRITE_CONV[GSYM LAPPEND] >>
    metis_tac[llist_wbisim_trans, llist_strip_NONE_nil_wbisim]) >-
   (disj1_tac >>
    ‘strip_NONE (h:::t) [||]’ by metis_tac[llist_wbisim_strip_NONE_nil,
                                           strip_NONE_cases, llist_wbisim_sym] >>
    rewrite_tac[Once $ GSYM LAPPEND] >>
    metis_tac[llist_wbisim_trans, llist_strip_NONE_nil_wbisim, llist_wbisim_sym]) >-
   (disj2_tac >>
    Cases_on ‘h’ >> Cases_on ‘h'’ >> fs[llist_wbisim_NONE] >-
     (metis_tac[]) >-
     (disj2_tac >>
      drule_then strip_assume_tac llist_wbisim_SOME_strip_NONE >>
      qexistsl_tac [‘ls ++ₗ r1’,‘t' ++ₗ r2’,‘x’] >>
      simp[strip_NONE_LAPPEND_SOME_strip_NONE, Once strip_NONE_cases] >>
      metis_tac[llist_wbisim_sym]) >-
     (disj2_tac >>
      drule_then strip_assume_tac llist_wbisim_SOME_strip_NONE_sym >>
      qexistsl_tac [‘t ++ₗ r1’,‘ls ++ₗ r2’,‘x’] >>
      simp[strip_NONE_LAPPEND_SOME_strip_NONE, Once strip_NONE_cases] >>
      metis_tac[]) >-
     (disj2_tac >>
      qexistsl_tac [‘t ++ₗ r1’,‘t' ++ₗ r2’,‘x’] >>
      simp[Once strip_NONE_cases] >> simp[Once strip_NONE_cases] >>
      subgoal ‘x = x' ∧ llist_wbisim t t'’ >-
       (pop_assum kall_tac >>
        fs[Once llist_wbisim_cases] >> gvs[Once strip_NONE_cases] >>
        gvs[Once strip_NONE_cases] >>
        metis_tac[llist_wbisim_cases, strip_NONE_cases]) >>
      metis_tac[])
   )
QED

CoInductive even_ollist:
  even_ollist [||] ∧
  (∀x xs. EVEN x ∧ even_ollist xs ⇒ even_ollist (SOME x:::xs)) ∧
  (∀xs. even_ollist xs ⇒ even_ollist (NONE:::xs))
End

Theorem even_ollist_NONE:
  even_ollist (NONE:::xs) = even_ollist xs
Proof
QED

(* you may need some lemmas about even_ollist and strip_NONE *)
Theorem wbisim_imp_even_ollist:
  ∀l' l. even_ollist l ∧ llist_wbisim l l' ⇒ even_ollist l'
Proof
QED

Theorem even_ollist_LAPPEND:
  even_ollist l ∧ even_ollist l' ⇒
  even_ollist (LAPPEND l l')
Proof
QED
