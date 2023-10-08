theory Scratch imports Main
begin

term "x"
term "\<lambda>x. x"
term "Suc 5"

declare[[show_types=false]]

text \<open> mark a type \<close>
lemma ext_imp:
  "(x::int) > 0 \<and> y > 0 \<longrightarrow> x+y > 0"
  apply(rule impI)
  apply(simp)
  done  

text \<open> refl \<close>
lemma alpha:
  "\<forall>t. (\<lambda>x. x) t = (\<lambda>y. y) t"
  apply(rule allI)
  apply(rule refl)
  done

text \<open> always erule mp \<close>
lemma "B \<longrightarrow> C \<Longrightarrow> A \<longrightarrow> B \<Longrightarrow> A \<longrightarrow>C"
  apply(rule impI)
  apply(erule mp)
  apply(erule mp, assumption)
  done

text \<open> chaining de morgan's \<close>
lemma "\<not>A \<or> \<not>B \<longrightarrow> \<not>(A \<and> B)"
  apply(rule impI, rule notI)
  apply(erule disjE)
   apply(drule conjunct1, erule notE, assumption)
  apply(drule conjunct2, erule notE, assumption)
  done

text \<open> cases \<close>
lemma "(\<not>P \<longrightarrow> False) \<longrightarrow> P"
  apply(rule impI)
  apply(cases P)
   apply(assumption)
  apply(drule mp)
  apply assumption
  apply(erule FalseE)
  done

text \<open> classical introduces notP and nothing else \<close>
lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply(rule impI)
  apply(rule classical)
  apply(erule impE)
   apply(rule impI)
   apply(erule notE, assumption)
  apply(assumption)
  done

thm someI
lemma "\<exists>x. P x \<Longrightarrow> P (SOME x. P x)"
  apply(erule exE)
  apply(rule_tac P=P and x=x in someI)
  apply assumption
  done

text \<open> eps elimination \<close>
lemma epsE: "P (SOME x. P x) \<Longrightarrow> \<exists>x. P x"
  apply(rule_tac x="SOME x. P x" in exI)
  apply(assumption)
  done

text \<open> safe rules \<close>
lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
  apply(rule allI, erule exE)
  apply(rule exI)
  apply(erule allE)
  apply(assumption)
  done

text \<open> clarify \<close>
lemma "(\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)" 
  apply(rule iffI)
  apply(clarify)
   apply(erule allE, erule mp, assumption)
  apply(clarify)
  apply(erule notE, rule exI, assumption)
  done
thm someI
text \<open> use SOME to delay choice for later instantiation \<close>
lemma choice:
  "\<forall>x. \<exists>y. R x y \<Longrightarrow> \<exists>f. \<forall>x. R x (f x)"
  apply(rule exI[where x="\<lambda>x. SOME y. R x y"])
  apply(rule allI)
  apply(erule allE)
  apply(erule exE)
  apply(rule someI)
  apply(assumption)
  done

(* ISAR schematic theorem, instantiating forall with fix *)
lemma assumes ex: "\<exists>x. \<forall>y. P x y" shows "\<forall>y. \<exists>x. P x y"
proof
  fix y
  from ex obtain x where "\<forall>y. P x y" ..
  from this have  "P x y" ..
  from this show   "\<exists>x. P x y" ..
qed

lemma
  assumes A: "\<forall>x y. P x y \<and> Q x y"
  shows "\<exists>x y. P x y \<and> Q x y"
proof -
  from A obtain x y where P: "P x y" and Q: "Q x y" by fast
  thus ?thesis by blast
qed

(* OF instantiation, arithmetic *)
lemma "\<exists>x::nat. (x div 2) * 2 = 0 * x"
  apply(rule_tac x=0 in exI)
thm ssubst
thm ssubst[OF div_0]
  apply(rule ssubst[OF div_0])
  apply(rule ssubst[OF mult_0[where n=2]])
  apply(rule ssubst[OF mult_0[where n=0]])
  apply(rule refl)
  done

(* this rewriting is automated by Isabelle's rewrite-engine, called the
   simplifier. This is what we will be learning about today. *)
lemma "\<exists>x::nat. (x div 2) * 2 = 0 * x"
  apply(rule_tac x=0 in exI)
  apply(simp only: div_0 add: mult_0)
  done

(* instantiate before automation, or use metis *)
lemma "\<exists>x::nat. (x div 2) * 2 = 0 * x"
  apply(metis div_0 mult_0)
  done

find_theorems "(_ + _) + _ = _ + (_ + _)"

(* GSYM equivalent, pass del: the original theorem *)
thm add_mult_distrib2[symmetric]

declare [[simp_trace=true]]

(* auto to first n goals, auto simp is better? *)
(* fastforce only touches current goal, arith solves linear equations *)
lemma "True \<and> ((\<exists>u::nat. x=y+u) \<longrightarrow> a*(b+c)+y \<le> x + a*b+a*c)"
  apply(auto)[1]
  apply(simp (no_asm) add: add_mult_distrib2 split: nat.split)
  done

declare [[simp_trace=false]]

(* [intro/elim/dest like conjunct1] *)
(* [cong] PQ = P' Q' by lifting P = Q*)
thm disj_cong imp_cong
lemma "\<lbrakk> P = P'; P' \<Longrightarrow> Q = Q' \<rbrakk> \<Longrightarrow> (P \<longrightarrow> Q) = (P' \<longrightarrow> Q')"
  apply(erule ssubst)
  apply(rule iffI)
   apply(rule impI)
   apply(drule mp, assumption)
   apply(drule mp[OF impI], assumption)
   apply(erule subst, assumption)
  apply(rule impI)
  apply(drule mp, assumption)
  apply(drule mp[OF impI], assumption)
  apply(erule ssubst, assumption)
  done

(* control click to browse source *)
term Eps
thm Let_def

(* add splits *)
lemma "\<lbrakk> (if x then z else \<not>z) = z \<rbrakk> \<Longrightarrow> x"
  apply(simp split: if_splits)
  done

end