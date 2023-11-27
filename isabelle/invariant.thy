theory week10B_demo
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
  by (simp_all add: distrib_left mult.commute)


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
  by (simp_all add: distrib_left mult.commute)

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
    apply(simp_all)
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
  apply(simp_all)
  by (metis (no_types, lifting) append_eq_append_conv2 list.collapse rev.simps(2) rev_append rev_is_rev_conv self_append_conv2)

lemma
  "VARS (A::int) (B::nat) (C::int)
   { a\<ge>0 }
    A:=a;
    B:=b;
    C:=1;
    WHILE B \<noteq> 0
    INV { TODO } DO
      WHILE ((B mod 2) = 0) 
      INV { TODO } DO
        A:=A*A;
        B:=B div 2
      OD;
      C := C * A; 
      B := B - 1
    OD
    { C = (a^b) }"
  apply(vcg)
  sorry

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
thm List_def Path.simps

(* "List nxt p Ps" represents a linked list, starting
    at pointer p, with 'nxt' being the function to find
    the next pointer, and Ps the list of all the content
    of the linked list *)

(* define a function that takes X, p and nxt function,
   assuming that X in the set of the linked list,
   then it returns the pointer to that element *)

(* think about its loop invariant *)

lemma
 "VARS nxt p
  { List nxt p Ps \<and> X \<in> set Ps }
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV { TODO }
  DO p := p^.nxt OD
  {  p = Ref X }"
  (* TODO *)
  sorry




(* define a function that "splices" 2 disjoint linked lists together *)

(* think about its loop invariant *)

lemma "VARS tl p q pp qq
  {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {} \<and> size Qs \<le> size Ps}
  pp := p;
  WHILE q \<noteq> Null
  INV {TODO}
  DO qq := q^.tl; q^.tl := pp^.tl; pp^.tl := q; pp := q^.tl; q := qq OD
  {List tl p (splice Ps Qs)}"
  (* todo*)
  sorry


end