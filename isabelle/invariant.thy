theory invariant
imports "~~/src/HOL/Hoare/HeapSyntax"
begin

lemma
  "VARS (A::int) B
   { True }
    A:=0;
    B:=0;
    WHILE A \<noteq> a
    INV { B = A * b } DO
      B := B + b;
      A := A + 1
    OD
    { B = a * b }"
  apply(vcg)
  by (simp add: distrib_left mult.commute)+

lemma
  "VARS (A::int) B
   { a\<ge>0 }
    A:=0;
    B:=0;
    WHILE A < a
    INV { B = A * b \<and> A \<le> a } DO
      B := B + b;
      A := A + 1
    OD
    { B = a * b }"
  apply(vcg)
  by (simp add: distrib_left mult.commute)+

lemma
  "VARS (A::nat) (B::int)
   { b\<ge>0 }
    A:=a;
    B:=1;
    WHILE A \<noteq> 0
    INV { A \<le> a \<and> B = b^(a - A) } DO
      B := B * b;
      A := A - 1
    OD
    { B = (b^a) }"
  apply(vcg)
    apply(auto)
  apply(subgoal_tac "Suc a - A = Suc (a-A)")
   apply(simp)
  apply(presburger)
  done

lemma
  "VARS (X::int list) (Y::int list)
   { True }
    X:=x;
    Y:=[];
    WHILE X \<noteq> []
    INV { rev X @ Y = rev x } DO
      Y := (hd X # Y);
      X := tl X
    OD
    { Y = rev x }"
  apply(vcg)
    apply(auto)
  by (metis (no_types) append_eq_append_conv2 list.collapse rev.simps
      rev_append rev_is_rev_conv self_append_conv2)

lemma
  "VARS (A::int) (B::nat) (C::int)
   { a\<ge>0 }
    A:=a;
    B:=b;
    C:=1;
    WHILE B \<noteq> 0
    INV { C * A^B = a^b \<and> (B=b \<or> B mod 2 = 0) } DO
      WHILE ((B mod 2) = 0)
      INV { C * A^B = a^b } DO
        A := A*A;
        B := B div 2
      OD;
      C := C * A;
      B := B - 1
    OD
    { C = (a^b) }"
  apply(vcg)
      apply(simp_all)
   apply(subgoal_tac "(A*A)^(B div 2) = A^B")
    apply(simp)
   apply(metis dvd_mult_div_cancel mod_0_imp_dvd power2_eq_square power_mult)
  apply(safe)
   apply(subgoal_tac "A * A^(B-Suc 0) = A^B")
    apply(simp add: mult.assoc)
   apply(metis One_nat_def mod_less_eq_dividend not_one_le_zero power_eq_if)
  apply(simp)
  by (metis One_nat_def dvd_imp_mod_0 dvd_minus_mod one_neq_zero)

lemma
  "VARS (A::int) (B::nat) (C::int)
   { a\<ge>0 }
    A:=a;
    B:=b;
    C:=1;
    WHILE B \<noteq> 0
    INV { a^b = C*A^B } DO
      WHILE ((B mod 2) = 0)
      INV { a^b = C*A^B } DO
        A:=A*A;
        B:=B div 2
      OD;
      C := C * A;
      B := B - 1
    OD
    { C = (a^b) }"
  apply(vcg)
  apply(simp_all)
   apply (metis dvd_mult_div_cancel mod_0_imp_dvd power2_eq_square power_mult)
  by (metis One_nat_def mod_less_eq_dividend not_one_le_zero power_eq_if)

text \<open>Pointers\<close>

(* "List nxt p Ps" represents a linked list, starting at pointer p,
    with 'nxt' being the function to find the next pointer,
    and Ps the list of all the content of the linked list *)
(* Ref parametrizes a word size *)

lemma
 "VARS nxt p
  { List nxt p Ps \<and> X \<in> set Ps }
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV { \<exists>Ps. List nxt p Ps \<and> X \<in> set Ps }
  DO p := p^.nxt OD
  { p = Ref X }"
  apply(vcg)
  by auto



value "splice [1,2,3::nat] [4,5,6]"
lemma splice1:
  "length Qs \<le> length Ps \<Longrightarrow>
   splice (take (length Qs) Ps) Qs @ (drop (length Qs) Ps) = splice Ps Qs"
  apply(induct Qs arbitrary: Ps)
   apply(simp)
  apply(auto)
  by (smt (verit) Cons_eq_appendI Suc_le_length_iff drop_Suc_Cons
                  splice.simps(2) take_Suc_Cons)

lemma drop_suc_take:
  "drop n ls = a # as \<and> take n ls = bs \<Longrightarrow> take (Suc n) ls = bs @ [a]"
  apply(induct ls arbitrary: as bs)
   apply(simp)
  by (smt drop_all list.discI list.sel take_hd_drop verit_comp_simplify1)

lemma splice_appl:
  "length la = length lb \<Longrightarrow>
   splice (la @ [a]) lb = splice la lb @ [a]"
  apply(induct la arbitrary: lb;simp)
  by (case_tac lb;simp)

lemma splice_appr:
  "length la = length lb + 1 \<Longrightarrow>
   splice la (lb @ [b]) = (splice la lb) @ [b]"
  apply(induct la arbitrary: lb;simp)
  by (case_tac lb;simp)

lemma splice_app2:
  "length la = length lb \<Longrightarrow>
   splice (la @ [a]) (lb @ [b]) = ((splice la lb) @ [a]) @ [b]"
  apply(simp add: splice_appr) (* cong @[b] *)
  by (erule splice_appl)

lemma splice2:
  "\<lbrakk>drop n Qs = y # bs; drop n Ps = a # ls\<rbrakk>
       \<Longrightarrow> splice (take (Suc n) Ps) (take (Suc n) Qs) =
           (splice (take n Ps) (take n Qs)) @ [a, y]"
  apply(cases "take n Ps"; cases "take n Qs")
     apply(auto simp add: drop_suc_take)
  apply(subgoal_tac "length list = length lista")
   apply(simp add: splice_app2)
  by (metis diff_diff_cancel drop_eq_Nil2 length_Cons length_drop length_rev list.distinct(1) nat.inject nat_le_linear rev_take)

lemma splice_set:
  "set (splice la lb) = set (la @ lb)"
  by (simp add: set_shuffles)

(* interleaves two lists. size invars always hold, p not modified *)
lemma "VARS tl p q pp qq
  { List tl p Ps \<and> List tl q Qs
  \<and> set Ps \<inter> set Qs = {} \<and> size Qs \<le> size Ps }
  pp := p;
  WHILE q \<noteq> Null
  INV { distinct Ps \<and> distinct Qs \<and>
        set Ps \<inter> set Qs = {} \<and> size Qs \<le> size Ps \<and>
       (\<exists>n. List tl pp (drop n Ps) \<and> List tl q (drop n Qs) \<and>
         (n \<le> size Qs) \<and>
        (Path tl p (splice (take n Ps) (take n Qs)) pp \<and>
         List tl pp (drop n Ps)))
  }
  DO qq := q^.tl; q^.tl := pp^.tl; pp^.tl := q; pp := q^.tl; q := qq OD
  { List tl p (splice Ps Qs) }"
  apply(vcg)
    apply(clarsimp)
    apply(rule_tac x=0 in exI)
    apply(simp)
   apply(clarsimp)
   apply(rule_tac x="Suc n" in exI)
   apply(subgoal_tac "((tl(y := tl (addr pp)))(pp \<rightarrow> Ref y)) y = tl (addr pp)")
    prefer 2
    apply(metis List_Ref List_conv_islist_list List_def Path.simps(1) addr.simps disjoint_iff drop_eq_Nil2 fun_upd_other fun_upd_same inf.bounded_iff inf.order_iff inf_left_idem list.set_intros(1) not_Null_eq set_drop_subset)
   apply(clarsimp)
   apply(rule conjI)
    defer
    apply(rule conjI)
     apply (smt (verit, ccfv_SIG) Cons_nth_drop_Suc List_def List_hd_not_in_tl Path.simps(2) addr.simps append_take_drop_id disjoint_iff le_neq_implies_less le_trans list.sel(3) list.set_intros(1) not_distinct_conv_prefix notin_List_update set_drop_subset subset_code(1) take_all)
    apply(rule conjI)
     apply (metis drop_all list.discI not_less_eq_eq)
    apply(rule conjI)
     prefer 3
     apply(clarsimp)
     apply (metis List_app splice1)
    apply(case_tac "drop n Ps")
     apply (metis drop_eq_Nil le_trans list.discI)
    apply(clarsimp simp add: splice2)
    apply(subgoal_tac "a \<notin> set (take n Qs) \<and> y \<notin> set (take n Ps) \<and>
                     a \<notin> set (take n Ps) \<and> y \<notin> set (take n Qs)")
     apply(simp add: splice_set)
    apply (metis Int_iff append_take_drop_id distinct_take empty_iff in_set_conv_decomp in_set_takeD not_distinct_conv_prefix)
   apply (smt (verit, del_insts) Cons_nth_drop_Suc List_def List_distinct Path.simps(2) addr.simps append_take_drop_id disjoint_iff distinct.simps(2) le_neq_implies_less le_trans list.set_intros(1) not_distinct_conv_prefix notin_List_update set_drop_subset subset_code(1) take_all)+
  done

lemma "VARS tl p q pp qq
  {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {} \<and> size Qs \<le> size Ps}
  pp := p;
  WHILE q \<noteq> Null
  INV {\<exists>as bs qs.
    distinct as \<and> Path tl p as pp \<and> List tl pp bs \<and> List tl q qs \<and>
    set bs \<inter> set qs = {} \<and> set as \<inter> (set bs \<union> set qs) = {} \<and>
    size qs \<le> size bs \<and> splice Ps Qs = as @ splice bs qs}
  DO qq := q^.tl; q^.tl := pp^.tl; pp^.tl := q; pp := q^.tl; q := qq OD
  {List tl p (splice Ps Qs)}"
  apply (vcg)
    apply simp_all
    apply(rule_tac x = "[]" in exI)
    apply fastforce
   apply clarsimp
   apply(rename_tac y bs qqs)
   apply(case_tac bs;clarsimp)
   apply(rename_tac x bbs)
   apply(rule_tac x = "as @ [x,y]" in exI)
   apply simp
   apply(rule_tac x = "bbs" in exI)
   apply simp
   apply(rule_tac x = "qqs" in exI)
   apply simp
  apply (auto simp: List_app)
  done

end