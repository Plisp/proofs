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
  apply(erule splice_appl)
  done

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

lemma test2:
  "\<And>tl p pp n y bs.
       \<lbrakk>set Ps \<inter> set Qs = {}; length Qs \<le> length Ps; List tl pp (drop n Ps);
        n \<le> length Qs; Path tl p (splice (take n Ps) (take n Qs)) pp;
        drop n Qs = y # bs; List tl (tl y) bs; 0 < n \<or> pp \<noteq> p\<rbrakk>
       \<Longrightarrow> List ((tl(y := tl (addr pp)))(pp \<rightarrow> Ref y)) (tl (addr pp))
            (drop (Suc n) Ps)"
  apply(cases Ps;clarsimp)
  apply(subgoal_tac "List tl (tl (addr pp)) (drop (Suc n) (a # list))")
  using notin_List_update
   apply(smt List_hd_not_in_tl disjoint_iff drop_Suc in_set_dropD list.sel list.set_intros)
  apply(subgoal_tac "n \<noteq> Suc (length list)")
   apply(smt (verit) Cons_nth_drop_Suc List_def Path.simps(2) addr.simps le_neq_implies_less le_trans length_Cons)
  apply(auto) (* n < length Qs \<le> Suc(length list) *)
  done

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
        ((n = 0 \<and> pp = p) \<or>
         Path tl p (splice (take n Ps) (take n Qs)) pp \<and>
         List tl pp (drop n Ps)))
  }
  DO qq := q^.tl; q^.tl := pp^.tl; pp^.tl := q; pp := q^.tl; q := qq OD
  { List tl p (splice Ps Qs) }"
  apply(vcg)
    apply(fastforce)
   defer
   apply(clarsimp)
   apply(case_tac "Qs = [] \<and> pp = p";clarsimp)
  using splice1 List_app
   apply(smt (verit) List_def List_distinct Path.simps(2) neq_dP)
  apply(clarsimp)
  apply(subgoal_tac "((tl(y := tl (addr pp)))(pp \<rightarrow> Ref y)) y = tl (addr pp)")
   defer
   apply(metis List_Ref List_conv_islist_list List_def Path.simps(1) addr.simps disjoint_iff drop_eq_Nil2 fun_upd_other fun_upd_same inf.bounded_iff inf.order_iff inf_left_idem list.set_intros(1) not_Null_eq set_drop_subset)
  apply(simp)
  apply(thin_tac "((tl(y := tl (addr pp)))(pp \<rightarrow> Ref y)) y = tl (addr pp)")
  apply(rule_tac x="Suc n" in exI)
  apply(case_tac "n = 0 \<and> pp = p";clarsimp)
   apply(rule conjI)
    apply(smt (verit) List_def List_distinct Path.simps(2) Suc_le_length_iff addr.simps distinct.simps(2) drop0 drop_Suc_Cons in_set_dropD notin_List_update)
   apply(rule conjI)
    apply(metis Int_iff List_def List_distinct Path.simps(2) Suc_le_length_iff addr.simps distinct.simps(2) distinct_length_2_or_more empty_iff notin_List_update)
   apply(rule conjI)
    apply(smt (verit) List_def Path.simps Suc_le_length_iff addr.simps fun_upd_other fun_upd_same insert_iff list.set(2) splice.simps(2) splice_Nil2 take0 take_Suc_Cons)
   apply(smt (verit) List_def List_distinct Path.simps(2) Suc_le_length_iff addr.simps distinct.simps(2) drop0 drop_Suc_Cons in_set_dropD notin_List_update)
  apply(simp add: test2)
  apply(rule conjI)
   apply(subgoal_tac "List tl (tl y) (drop (Suc n) Qs)")
  using notin_List_update
    apply(metis Cons_nth_drop_Suc List_def List_hd_not_in_tl Path.simps(2) addr.simps disjoint_iff drop_all in_set_dropD le_neq_implies_less le_trans list.set_intros(1))
   apply(metis drop_Suc list.sel(3) tl_drop)
  apply(rule conjI)
   apply(metis drop_all leI le_less_Suc_eq list.discI)
  (* final case *)
  apply(case_tac "drop n Ps")
   apply(simp)
  apply(subgoal_tac "splice (take (Suc n) Ps) (take (Suc n) Qs)
                   = splice (take n Ps) (take n Qs) @ [a,y]")
   defer
   apply(simp add: splice2)
  apply(clarsimp)
  apply(thin_tac "splice (take (Suc n) Ps) (take (Suc n) Qs)
                = splice (take n Ps) (take n Qs) @ [a, y]")
  apply(rule conjI)
   defer
   apply(metis Int_iff empty_iff fun_upd_same fun_upd_twist in_set_dropD list.set_intros(1))
  apply(subgoal_tac "a \<notin> set (take n Qs) \<and> y \<notin> set (take n Ps) \<and>
                     a \<notin> set (take n Ps) \<and> y \<notin> set (take n Qs)")
   apply(simp add: splice_set)
  apply(metis append_take_drop_id disjoint_iff distinct_take in_set_dropD in_set_takeD list.set_intros(1) not_distinct_conv_prefix)
  done

(* unused
lemma Path_app:
  "\<And>tl. Path tl p la pp \<Longrightarrow> Path tl pp lb ppp
     \<Longrightarrow> Path tl p (la @ lb) ppp"
  apply(induct la arbitrary: p)
  by auto
*)
end