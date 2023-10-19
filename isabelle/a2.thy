theory a2
  imports Main
begin


section "1. Lists as multisets"


text \<open>
This question explores lists as multisets. A list @{term "[0,0,0,2,1,3,2]"}
can be seen as a multiset containing 0,1,2,3, with multiplicity 3,1,2,1, respectively.

Isabelle has a built-in function @{term count_list} that gives multiplicity
\<close>
value "count_list [0::nat,0,0,2,1,3,2] (0::nat)"
text \<open>
In the following, instead of using this count_list,
 we define multiplicity as a finite map @{term m_count} and
 prove some properties about it.

In working on these questions, the @{text ext} lemma can be useful.
Also, it is often useful (and necessary) to fine control the simplifier
 by using "simp only:", "simp (no_asm_simp)", etc.
\<close>


subsection "1.1 Multiplicity function for lists as multisets"

text \<open> We define {@term m_count}, as below. It converts a list as a multiset
 to a function that returns @{term "nat option"}:
 @{term "m_count ls x"} returns @{term None}
if @{term x} does not appear in @{term ls} and returns @{term "Some n"}
 if @{term x} appears @{term "n+1"} times in @{term ls}.
 The @{term nat} value is offset by 1 because we start from
@{term "Some 0"} when @{term x} appears once in @{term ls}.
\<close>
primrec m_count :: "'a list \<Rightarrow> ('a, nat) map" where
  "m_count [] = Map.empty" (* K NONE *)
| "m_count (a#as) =
    (case (m_count as) a of
       None \<Rightarrow> (m_count as)(a\<mapsto>0)
     | Some n \<Rightarrow> (m_count as)(a\<mapsto>Suc n))"

value "m_count [0::nat,0,0,2,1,3,2] 0"
value "count_list [0::nat,0,0,2,1,3,2] 0"

text \<open>
1-(a) State the correspondence between Isabelle's @{term count_list} and
 @{term m_count} as logical equality and prove it.
\<close>
lemma m_count_corres0:
  "(m_count ls x = None \<longleftrightarrow> count_list ls x = 0)"
  apply(induct ls)
   apply(simp)
  apply(simp)
  apply(rule conjI)
   apply(case_tac "m_count ls x")
    apply(simp)
   apply(fastforce)
  apply(case_tac "m_count ls a")
   apply(simp)
  apply(simp)
  done

lemma m_count_corres2: "(m_count ls x = None \<longleftrightarrow> count_list ls x = 0) \<and>
                       (m_count ls x = Some n \<longleftrightarrow> count_list ls x = n+1)"
  apply(rule conjI)
   apply(simp add: m_count_corres0)
  apply(induct ls arbitrary: n)
   apply(simp)
  apply(drule_tac allI)
  apply(rename_tac m)
  apply(simp)
  apply(rule conjI)
   apply(case_tac "m_count ls x")
    apply(drule_tac x=n in allE)
     apply(simp)
    apply(simp)
    apply(simp add: m_count_corres0)
   apply(simp)
   apply(fastforce)
  apply(case_tac "m_count ls a")
   apply(simp)
  apply(simp)
  done

lemma m_count_corres: "count_list ls x = n \<longleftrightarrow> m_count ls x = (if n=0 then None else Some (n-1))"
  apply(simp add: m_count_corres2)
  done

text \<open>
1-(b) Prove that @{term "m_count ls x = None"} is equivalent to
 @{term x} not being a member of @{term ls}.
\<close>
find_theorems "count_list"
lemma m_notin: "m_count ls x = None \<longleftrightarrow> x \<notin> set ls"
  by (auto simp add: m_count_corres2 count_list_0_iff)


subsection "1.2 Ordering on multisets"

text \<open>
We can define an ordering on multisets: @{term "ls1 \<le> ls2"} holds if,
 for any @{term "x::'a"}, the multiplicity of @{term x} is higher in
 @{term ls2} than in @{term ls1}. This ordering is defined
in terms of @{term m_count} as below:
\<close>

definition le :: "('a, nat) map \<Rightarrow> ('a, nat) map \<Rightarrow> bool" where
  "le m1 m2 \<equiv>
      \<forall>x. case (m1 x, m2 x) of
            (Some a, Some b) \<Rightarrow> a \<le> b
          | (Some a, None) \<Rightarrow> False
          | (None, _) \<Rightarrow> True"


text \<open>
1-(c) Give two examples of multisets @{term my_ls1}, @{term my_ls2} such that
 @{term "le (m_count my_ls1) (m_count my_ls2)"} holds.
 Then show that @{term le} is defined correctly by proving it.
\<close>
(* replace the two undefined below with your multisets *)
definition "my_ls1 = []"
definition "my_ls2 = []"

lemma le_example: "le (m_count my_ls1) (m_count my_ls2)"
  apply(unfold le_def my_ls1_def my_ls2_def)
  apply(simp)
  done


text \<open>
1-(d) Prove that adding an element to a list by @{term Cons} always gives a list
  greater than the original list.\<close>

lemma le_m_count: "le (m_count ls) (m_count (x#ls))" 
  apply(unfold le_def)
  apply(clarify)
  apply(case_tac "xa=x")
   apply(case_tac "m_count ls xa")
    apply(simp)
   apply(simp)
  apply(case_tac "m_count ls xa")
   apply(simp)
  apply(simp)
  apply(case_tac "m_count ls x")
   apply(simp)
  apply(simp)
  done


text \<open>
1-(e) Prove that @{term m_count} is preserved
  by changing the order of the elements in the list.
\<close>
lemma m_count_switch:
  "m_count (x # a # ys) = m_count (a # x # ys)"
  apply(rule ext)
  apply(simp split: option.split)
  done

lemma m_count_perm:
  "ls = xs @ (x # ys)  \<Longrightarrow> m_count ls = m_count (x # (xs @ ys))"
proof(induct xs arbitrary: ys ls)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  hence "m_count (xs @ x # ys) = m_count (x # xs @ ys) \<and>
         ls = a # (xs @ x # ys)"
    by simp
  hence "m_count ls = m_count (a # (x # xs @ ys))"
    by (auto simp add: m_count_def)
  then show ?case
    by (simp only: m_count_switch List.append.append_Cons)
qed


subsection "1.3 Addition of multisets"

text \<open>Next, we consider addition of two multisets. For lists as multisets,
 this corresponds to @{term append}. We can also consider addition of
 multiplicity functions, which is defined for
@{term m_count} as below: \<close>

definition m_add :: "('a, nat) map \<Rightarrow> ('a, nat) map \<Rightarrow> ('a,nat) map" where
  "m_add m1 m2 \<equiv>
      \<lambda>x. case (m1 x, m2 x) of
           (Some a, Some b) \<Rightarrow> Some (a + b + 1)
          | (Some a, None) \<Rightarrow> m1 x
          | (None, _) \<Rightarrow> m2 x"

text \<open>
1-(f) Prove that the empty map is an identity for addition of maps
 (both for left and right).
\<close>

lemma m_add_empty[simp]: "m_add Map.empty m = m"
  apply(auto simp: m_add_def)
  done

lemma m_add_empty2[simp]: "m_add m Map.empty = m"
  apply(rule ext)
  apply(case_tac "m x")
   apply(simp add: m_add_def)
  apply(simp add: m_add_def)
  done


text \<open>
1-(g) Prove that @{term m_add} correctly returns the multiplicity of 
added multisets, i.e., two lists appended by Isabelle @{term append}.
\<close>

lemma m_count_x_not_a: "a \<noteq> x \<Longrightarrow> m_count (a # ls) x = m_count ls x"
  apply(simp split: option.splits)
  done

lemma m_count_x_eq_a: "m_count ls x = None \<Longrightarrow> m_count (x # ls) x = Some 0 \<and>
                       m_count ls x = Some k \<Longrightarrow> m_count (x # ls) x = Some (k+1)"
  apply(simp)
  done

(* massaging these trivialities into an Isabelle proof made me question my beliefs *)
(* I guess it's also possible to use the correspondence to count_list but... also annoying *)
lemma m_add_append: "m_add (m_count ls1) (m_count ls2) = m_count (append ls1 ls2)"
  apply(induct ls1)
   apply(simp)
  apply(simp only: List.append.append_Cons)
  apply(rule ext)
  apply(case_tac "a\<noteq>x")
   apply(subgoal_tac "m_add (m_count ls1) (m_count ls2) x 
                    = m_count (ls1 @ ls2) x")
    apply(insert m_count_x_not_a)[1]
    apply(drule_tac x=a in meta_spec)
    apply(drule_tac x=x in meta_spec)
    apply(drule_tac x=ls1 in meta_spec)
    apply(insert m_count_x_not_a)[1]
    apply(drule_tac x=a in meta_spec)
    apply(drule_tac x=x in meta_spec)
    apply(drule_tac x="ls1@ls2" in meta_spec)
    apply(drule mp[OF impI], assumption)
    apply(drule mp[OF impI], assumption)
    apply(drule_tac arg_cong)
    apply(simp only: m_add_def)
   apply(simp)
  (* I did the "easier" \<noteq> goal first, but it turned out harder *)
  thm SMT.smt_arith_simplify(277)
  apply(simp only: SMT.smt_arith_simplify)
  apply(clarify)
  apply(case_tac "m_count (ls1@ls2) x")
   apply(subgoal_tac "m_add (m_count (x # ls1)) (m_count ls2) x = Some 0")
    apply(simp)
   apply(drule ssubst, assumption)
   apply(simp only: m_add_def)
   apply(case_tac "m_count ls1 x")
    apply(simp)
   apply(simp add: m_count_x_eq_a)
   apply(case_tac "m_count ls2 x")
    apply(simp)
   apply(simp)
  apply(subgoal_tac "m_add (m_count (x # ls1)) (m_count ls2) x = Some (aa+1)")
   apply(simp)
  apply(drule ssubst, assumption)
  apply(thin_tac "m_count (ls1 @ ls2) x = Some aa")
  apply(simp only: m_add_def)
  apply(case_tac "m_count ls1 x")
   apply(simp)
  apply(simp add: m_count_x_eq_a)
  apply(case_tac "m_count ls2 x")
   apply(simp)
  apply(simp)
  done



subsection "1.4 Sorting of multisets"

text \<open>
Consider the simple sorting function defined as below:
\<close>

primrec insort' :: "'a::ord \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort' x [] = [x]" |
  "insort' x (y#ys) =
  (if x \<le> y then (x#y#ys) else y#(insort' x ys))"

definition sort' :: "('a::ord) list \<Rightarrow> 'a list" where
  "sort' xs = foldr insort' xs []"
find_theorems "foldr"

text \<open>
1-(h) With respect to the above sorting function, prove that the sorting of a list
does not change the multiset it represents; in other words, that @{term sort'}
preserves multiplicity.
\<close>
lemma m_count_consg:
  "m_count xs = m_count ys \<Longrightarrow> m_count (b#xs) = m_count (b#ys)"
  apply(simp add: m_count_def)
  done

lemma "m_count_insort":
  "m_count (insort' a ys) = m_count (a#ys)"
  apply(induct ys)
   apply(simp)
  apply(rename_tac b ys)
  apply(case_tac "a \<le> b")
   apply(simp)
  apply(simp only:m_count_switch)
  apply(subgoal_tac "m_count (b # (insort' a ys)) = m_count (b # (a # ys))")
   apply(simp)
  apply(erule m_count_consg)
  done

lemma m_count_sort_a:
  "m_count (sort' (a # ls)) = m_count (a # sort' ls)"
  apply(unfold sort'_def)
  apply(simp)
  apply(cases "(foldr insort' ls [])")
   apply(simp)
  apply(rename_tac y ys)
  apply(simp only:)
  apply(case_tac "a \<le> y")
   apply(simp)
  apply(simp only: m_count_insort)
  apply(simp)
  done

lemma m_count_sort':
  "m_count (sort' ls) = m_count ls"
  apply(induct ls)
   apply(simp add: sort'_def)
  apply(subgoal_tac " m_count (sort' (a # ls)) = m_count (a # sort' ls)")
   apply(erule trans)
  thm m_count_consg
  apply(erule m_count_consg)
  apply(rule m_count_sort_a)
  done


subsection "1.5 Union of multisets"

text \<open>
We now consider a union of two multisets, whose multiplicity can be
given by the following function:
\<close>
definition m_union :: "('a, nat) map \<Rightarrow> ('a, nat) map \<Rightarrow> ('a,nat) map" where
  "m_union m1 m2 \<equiv>
      \<lambda>x. case (m1 x, m2 x) of
            (Some a, Some b) \<Rightarrow> Some (max a b)
          | (Some a, None) \<Rightarrow> m1 x
          | (None, _) \<Rightarrow> m2 x"

text \<open>
The union @{text m_Un} of two lists as multisets can be defined as follows:
\<close>
primrec m_Un' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "m_Un' [] ys ac = ys @ ac"
| "m_Un' (x#xs) ys ac =
     (if x \<in> set ys then m_Un' xs (remove1 x ys) (x#ac)
      else m_Un' xs ys (x#ac))"

definition m_Un where "m_Un l1 l2 = m_Un' l1 l2 []"
declare [[simp]] m_Un_def

text \<open>
1-(i) Prove the following lemma about @{term m_Un'} and @{term append}.
\<close>
lemma ac_append:
  "m_Un' l1 l2 (ac @ ls) = (m_Un' l1 l2 ac) @ ls"
  apply(induct l1 arbitrary: l2 ac)
   apply(simp)
  apply(simp)
  apply(safe)
   apply(drule_tac x="(remove1 a l2)" in meta_spec)
   apply(drule_tac x="a#ac" in meta_spec)
   apply(simp)
  apply(drule_tac x="l2" in meta_spec)
  apply(drule_tac x="a#ac" in meta_spec)
  apply(simp)
  done

text \<open>
1-(j) Prove the following lemma about @{term remove1} and @{term m_count}.
\<close>

lemma count_list_remove1:
  "count_list ls a = Suc n \<Longrightarrow> count_list (remove1 a ls) a = n"
  apply(induct ls)
   apply(simp)
  apply(auto)
  done

lemma m_count_remove1_idem:
  "x \<noteq> a \<Longrightarrow> m_count (remove1 a ls) x = m_count ls x"
  apply(induct ls arbitrary: x)
   apply(simp)
  apply(case_tac "aa=x")
   apply(clarsimp)
  apply(case_tac "m_count ls x")
    apply(simp)
   apply(simp)
  apply(clarsimp)
  apply(rule conjI)
   apply(case_tac "m_count ls aa")
    apply(simp)
   apply(simp)
  apply(case_tac "m_count ls aa")
   apply(simp)
  apply(drule_tac x=x in meta_spec)
  apply(simp)
  done

lemma m_count_remove1:
  "m_count (remove1 a ls) =
    (case m_count ls a of
      None \<Rightarrow> m_count ls
    | Some n \<Rightarrow> if n = 0 then (m_count ls)(a := None)
                else (m_count ls)(a:= map_option (\<lambda>x. x - 1) (m_count ls a)))"
  apply(cases "m_count ls a")
   apply(simp)
   apply(simp add: m_notin List.remove1_idem)
  apply(auto)
   apply(rule ext)
   apply(case_tac "x=a")
    apply(simp)
    apply(subgoal_tac "count_list (remove1 a ls) a = 0")
     apply(simp add: m_count_corres)
    apply(simp add: m_count_corres2 count_list_remove1)
   apply(simp)
   apply(thin_tac "m_count ls a = Some 0")
   apply(simp add: m_count_remove1_idem)
  apply(rule ext)
  apply(case_tac "x\<noteq>a")
   apply(simp add: m_count_remove1_idem)
  apply(clarsimp)
  apply(simp add: m_count_corres2 count_list_remove1)
  done

text \<open>
1-(k) Prove the correctness of @{term m_Un} with respect to @{term m_union}.
\<close>
lemma count_list_remove1_inv:
  "a \<in> set ls \<Longrightarrow> count_list (remove1 a ls) a = n \<Longrightarrow> count_list ls a = Suc n"
  apply(induct ls)
   apply(simp)
  apply(auto)
  done

lemma count_list_remove1_one:
  "count_list (remove1 a ls) a = 0 \<Longrightarrow> count_list ls a = 1 \<or> count_list ls a = 0"
  apply(induct ls)
   apply(simp)
  apply(auto)
  done

lemma count_list_remove_other:
  "a\<noteq>x \<Longrightarrow> count_list (remove1 a ls) x = count_list ls x"
  apply(induct ls)
   apply(simp)
  apply(auto)
  done

lemma m_un_add: "count_list l1 x = a \<Longrightarrow> count_list l2 x = b \<Longrightarrow> count_list l3 x = c
             \<Longrightarrow> count_list (m_Un' l1 l2 l3) x = c + max a b"
  apply(induct l1 arbitrary: l2 l3 a b c)
   apply(simp)
  apply(auto)
   apply(case_tac "count_list (remove1 x l2) x")
    apply(simp)
    apply(drule count_list_remove1_one)
    apply(fastforce)
   apply(simp)
   apply(drule count_list_remove1_inv, assumption)
   apply(fastforce)
  apply(simp add: count_list_remove_other)
  done

(* wow this one is nice. isomorphism to use existing list theorems :D I see! *)
lemma m_count_union: "m_count (m_Un l1 l2) = m_union (m_count l1) (m_count l2)"
  unfolding m_union_def
  apply(rule ext)
  apply(case_tac "m_count l1 x")
   apply(case_tac "m_count l2 x")
    apply(simp)
    apply(subgoal_tac "count_list (m_Un l1 l2) x = 0")
     apply(simp add: m_count_corres2 m_Un_def)
    apply(simp add: m_count_corres2 m_un_add m_Un_def)
   apply(simp)
   apply(subgoal_tac "count_list (m_Un l1 l2) x = a+1")
    apply(simp add: m_count_corres2 m_Un_def)
   apply(simp add: m_count_corres2 m_un_add m_Un_def)
  apply(case_tac "m_count l2 x")
   apply(simp)
   apply(subgoal_tac "count_list (m_Un l1 l2) x = a+1")
    apply(simp add: m_count_corres2 m_Un_def)
   apply(simp add: m_count_corres2 m_un_add m_Un_def)
  apply(simp add: m_Un_def)
  apply(subgoal_tac "count_list (m_Un l1 l2) x = (max a aa) + 1")
   apply(simp add: m_count_corres2 m_Un_def)
  apply(simp add: m_count_corres2 m_un_add m_Un_def)
  done


(*---------------------------------------------------------*)


section "2. Compiler for arithmetic expressions"


(* Syntax of the language *)
type_synonym vname = string
type_synonym val = int

datatype aexp = N val | V vname | Plus aexp aexp

(* Evaluation function *)
type_synonym vstate = "vname \<Rightarrow> val"

primrec eval :: "aexp \<Rightarrow> vstate \<Rightarrow> val" where
  "eval (N n) s = n"
| "eval (V x) s = s x"
| "eval (Plus e1 e2) s = eval e1 s + eval e2 s"

(* Programs for the register machine *)
type_synonym reg = nat
datatype prog =
    LoadI reg val
  | Load reg vname
  | Add reg reg
  | Seq prog prog ("_ ;; _" 100)
  | Skip

(* Compiler from expression to register programs *)
primrec compile :: "aexp \<Rightarrow> reg \<Rightarrow> prog \<times> reg"
where
  "compile (N n) r = (LoadI r n, r + 1)" |
  "compile (V x) r = (Load r x, r + 1)" |
  "compile (Plus e1 e2) r1 =
    (let (p1, r2) = compile e1 r1;
         (p2, r3) = compile e2 r2
      in ((Seq p1 (Seq p2 (Add r1 r2))), r3))"


(* ---------- *)
text\<open>
2-(a): Give an example of an arithmetic expression which evaluates to 7 and uses @{term Plus}
    twice or more. Prove that your example actually evaluates to 7.
\<close>

value "(Plus (N 2) (Plus (N 1) (N 4)))"
lemma "eval (Plus (N 2) (Plus (N 1) (N 4))) (\<lambda>x. 0) = 7"
  apply(simp)
  done

text\<open>
2-(b): Prove that the compiler always returns a register identifier strictly higher
  than the one given to it.
\<close>
lemma compile_reg_increase:
  "compile e r = (p, r') \<Longrightarrow> r' > r"
  apply(induct e arbitrary: p r' r)
    apply(auto)
  apply(auto split: prod.splits)
  apply(fastforce)
  done

(* ---------- *)
subsection "2.1 Target machine big-step semantics and compiler correctness"

(* Big step operational semantics to programs for the register machine *)
type_synonym rstate = "reg \<Rightarrow> val"
type_synonym mstate = "rstate \<times> vstate \<times> prog"

inductive sem :: "mstate \<Rightarrow> rstate \<Rightarrow> bool"
  ("_ \<Down> _" [0,60] 61) where
  sem_LoadI: "(rs, \<sigma>, LoadI r n) \<Down> rs(r := n)"
| sem_Load: "(rs, \<sigma>, Load r v) \<Down> rs(r := \<sigma> v)"
| sem_Add: "(rs, \<sigma>, Add r1 r2) \<Down> rs(r1 := rs r1 + rs r2)"
| sem_Seq: "\<lbrakk>(rs, \<sigma>, p) \<Down> rs'; (rs', \<sigma>, q) \<Down> rs''\<rbrakk> \<Longrightarrow> (rs, \<sigma>, p ;; q) \<Down> rs''"
(* ---------- *)

text\<open>
2-(c): Prove that the register machine semantics is deterministic.
\<close>

lemma sem_det: "\<lbrakk>(rs, \<sigma>, e) \<Down> rs'; (rs, \<sigma>, e) \<Down> rs''\<rbrakk> \<Longrightarrow> rs' = rs''"
  apply(induct e arbitrary: rs rs' rs'')
      apply(erule sem.cases, simp_all)
      apply(erule sem.cases, simp_all)
     apply(erule sem.cases, simp_all)
     apply(erule sem.cases, simp_all)
    apply(erule sem.cases, simp_all)
    apply(erule sem.cases, simp_all)
   apply(erule sem.cases, simp_all)
   apply(erule sem.cases, simp_all)
   apply(clarsimp)
   apply(metis)
  apply(erule sem.cases, simp_all)
  done


text\<open>
2-(d): Prove that the compiler produces programs that do not modify any registers
  of identifier lower than the register identifier given to it.
\<close>

lemma compile_no_modify_lower_reg:
  "compile e r = (p, r') \<Longrightarrow>
   (rs, \<sigma>, p) \<Down> rs' \<Longrightarrow>
   r'' < r \<Longrightarrow>
   rs' r'' = rs r''"
  thm compile_reg_increase
  apply(induct e arbitrary: r r' r'' rs rs' p)
    apply(clarsimp)
    (* loadI evaluates to rs[r=x], equal rs' by sem_det, r'' < r *)
    apply (metis fun_upd_other nat_neq_iff sem_LoadI sem_det)
   apply(clarsimp)
   apply (metis fun_upd_other nat_neq_iff sem_Load sem_det)
  apply(simp split: prod.splits)
  by (smt (verit) compile_reg_increase sem_Add sem_det
      fun_upd_other nat_neq_iff order_less_trans prod.inject sem.simps
      prog.distinct(11) prog.distinct(15) prog.distinct(5) prog.inject(4))

text\<open>
2-(e): Prove that the compiler produces programs that, when executed, yield the value
  of the expression in the register *provided* as the argument to @{term compile} in
  the final @{term rstate} according to the program's big-step semantics.
\<close>

lemma compile_correct:
  "compile e r = (p, r') \<Longrightarrow>
   (rs, \<sigma>, p) \<Down> rs' \<Longrightarrow>
   rs' r = eval e \<sigma>"
  apply(induct e arbitrary: r r' rs rs' p)
  apply(simp)
    apply (metis fun_upd_same sem_LoadI sem_det)
  apply(simp)
   apply (metis fun_upd_same sem_Load sem_det)
  apply(simp split: prod.splits)
  by (smt (verit) compile_no_modify_lower_reg compile_reg_increase 
      sem_Add sem_det
      fst_conv snd_conv fun_upd_same sem.simps
      prog.distinct(11) prog.distinct(15) prog.distinct(5) prog.inject(4))


(* ---------- *)


(*  Small-step semantics *)
inductive s_sem :: "mstate \<Rightarrow> mstate \<Rightarrow> bool" ("_ \<leadsto> _" 100)
  where
  "(rs, \<sigma>, LoadI r n) \<leadsto> (rs(r := n), \<sigma>, Skip)"
| "(rs, \<sigma>, Load r v) \<leadsto> (rs(r := \<sigma> v), \<sigma>, Skip)"
| "(rs, \<sigma>, Add r1 r2) \<leadsto> (rs(r1 := rs r1 + rs r2), \<sigma>, Skip)"
| "(rs, \<sigma>, p) \<leadsto> (rs', \<sigma>, p') \<Longrightarrow> (rs, \<sigma>, p ;; q) \<leadsto> (rs', \<sigma>, p' ;; q)"
| "(rs, \<sigma>, Skip ;; p) \<leadsto> (rs, \<sigma>, p)"
print_theorems

primrec term_with_n_Suc :: "nat \<Rightarrow> aexp" where
  "term_with_n_Suc 0 = N 0"
| "term_with_n_Suc (Suc n) = (Plus (term_with_n_Suc n) (N 0))"
(* ---------- *)


text\<open>
2-(f): Define a function s_sem_n:: nat \<Rightarrow> mstate \<Rightarrow> mstate \<Rightarrow> bool
that executes n steps of the small-step semantics.
\<close>

primrec s_sem_n :: "nat \<Rightarrow> mstate \<Rightarrow> mstate \<Rightarrow> bool" where
  "s_sem_n 0       a b = (a = b)" |
  "s_sem_n (Suc n) a c = (\<exists>b. (a \<leadsto> b) \<and> s_sem_n n b c)"
print_theorems

text\<open>
2-(g): Prove that two executions of resp. n and m steps according to
   s_sem_n compose into a single execution of (n+m) steps if their
   resp. final and initial machine state match.
\<close>

lemma s_sem_n_add:
  "s_sem_n n ms ms' \<Longrightarrow> s_sem_n m ms' ms'' \<Longrightarrow> s_sem_n (n+m) ms ms''"
  apply(induct n arbitrary: ms)
   apply(simp)
  apply(subgoal_tac "\<lbrakk>\<And>ms. \<lbrakk>s_sem_n n ms ms'; s_sem_n m ms' ms''\<rbrakk>
              \<Longrightarrow> s_sem_n (n + m) ms ms'';
       \<exists>b. (ms \<leadsto> b) \<and> s_sem_n n b ms'; s_sem_n m ms' ms''\<rbrakk>
       \<Longrightarrow> s_sem_n (Suc n + m) ms ms''")
   apply(simp)
  apply(erule exE)
  apply(fastforce)
  done


text\<open>
2-(h): Prove that if p executes to p' in n steps according to s_sem_n, then
   p ;; q will execute to p' ;; q in n steps with all other parts of the
   state being the same as in the original execution.
\<close>
lemma s_sem_Seq:
  "s_sem_n (Suc n) (rs, \<sigma>, p) (rs', \<sigma>, p')
   \<Longrightarrow> \<exists>bs bp. ((rs, \<sigma>, p) \<leadsto> (bs, \<sigma>, bp)) \<and> s_sem_n n (bs, \<sigma>, bp) (rs', \<sigma>, p')"
  apply(clarsimp)
  using s_sem.cases
  apply(fastforce)
  done

lemma s_sem_n_Seq:
  "s_sem_n n (rs, \<sigma>, p) (rs', \<sigma>, p') \<Longrightarrow>
     s_sem_n n (rs, \<sigma>, p;;q) (rs', \<sigma>, p';;q)"
  apply(induct n arbitrary: rs p)
   apply(simp)
  apply(subgoal_tac "\<And>n rs.
       \<lbrakk>\<And>rs p. s_sem_n n (rs, \<sigma>, p) (rs', \<sigma>, p') \<Longrightarrow>
             s_sem_n n (rs, \<sigma>, p ;; q) (rs', \<sigma>, p' ;; q);
        \<exists>bs bp. ((rs, \<sigma>, p) \<leadsto> (bs, \<sigma>, bp)) \<and> s_sem_n n (bs, \<sigma>, bp) (rs', \<sigma>, p')\<rbrakk>
       \<Longrightarrow> s_sem_n (Suc n) (rs, \<sigma>, p ;; q)
            (rs', \<sigma>, p' ;; q)")
   apply(simp add: s_sem_Seq)
  apply(clarsimp)
  apply(thin_tac "\<And>rs p. s_sem_n n (rs, \<sigma>, p) (rs', \<sigma>, p') \<Longrightarrow>
              s_sem_n n (rs, \<sigma>, p ;; q)
               (rs', \<sigma>, p' ;; q)")
  apply(thin_tac "s_sem_n n (a, aa, b) (rs', \<sigma>, p')")
  apply(thin_tac "(rs, \<sigma>, p) \<leadsto> (a, aa, b)")
  apply(rule_tac x=bs in exI)
  apply(rule_tac x=\<sigma> in exI)
  apply(rule_tac x="bp;;q" in exI)
  apply(auto)
  apply(simp add: s_sem.intros)
  done


text\<open>
2-(i): Prove that if a program executes in the big-step semantics to a 
   resulting rstate rs', then it executes in the small-step semantics
   to the same resulting rstate and the resulting program Skip with
   no changes to the vstate.
\<close>
lemma s_sem_det:
  "(rs, \<sigma>, p) \<leadsto> b \<Longrightarrow> (rs, \<sigma>, p) \<leadsto> c \<Longrightarrow> b = c"
  apply(induct p arbitrary: rs)
      apply(erule s_sem.cases, simp_all)
      apply(erule s_sem.cases, simp_all)
     apply(erule s_sem.cases, simp_all)
     apply(erule s_sem.cases, simp_all)
    apply(erule s_sem.cases, simp_all)
    apply(erule s_sem.cases, simp_all)
  sorry

lemma s_sem_n_correct:
  "ms \<Down> rs' \<Longrightarrow> \<exists>n. s_sem_n n ms (rs', fst (snd ms), Skip)"
  apply(erule sem.induct)
     apply(simp_all del: Fun.fun_upd_apply)
     apply(rule exI[where x=1])
     apply(simp del: Fun.fun_upd_apply)
     apply(rule_tac s_sem.intros(1))
    apply (metis s_sem.intros s_sem_n.simps)
   apply (metis s_sem.intros s_sem_n.simps)
  apply(clarsimp)
  apply(meson s_sem.intros s_sem_n.simps s_sem_n_Seq s_sem_n_add)
  done


text\<open>
2-(j): Prove that compiling a "term_with_n_Suc h" will use a number of
   registers that is indeed strictly lower bounded by h.
\<close>

lemma compile_term_with_n_Suc_lower_bound_n:
   "h < snd (compile (term_with_n_Suc h) r) - r"
  apply(induct h)
   apply(simp)
  apply(auto split: prod.splits)
  done


text\<open>
2-(k): Using this fact, prove that there is no universal bound on the number
   of registers used for any compiled program.
\<close>

lemma compile_has_no_universal_register_bound:
  "\<not> (\<exists>h. (\<forall>p. h \<ge> snd (compile p r) - r))"
  apply(clarsimp)
  apply(rule_tac x="(term_with_n_Suc h)" in exI)
  apply(cut_tac h=h and r=r in compile_term_with_n_Suc_lower_bound_n)
  apply(fastforce)
  done


(*---------------------------------------------------------*)

end