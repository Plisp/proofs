theory exam
imports AutoCorres.AutoCorres
begin

declare [[syntax_ambiguity_warning=false]]
declare fun_upd_apply[simp]

text \<open>
  This theory is designed to be loaded with the AutoCorres logic image via e.g.
  L4V_ARCH=ARM isabelle jedit -d autocorres-1.10 -l AutoCorres exam.thy
\<close>

(*---------------------------------------------------------*)
(***********************)
(*     Question 1      *)
(***********************)

section \<open>Conceptual understanding questions\<close>

text \<open>
a) Which lambda-calculus term is both a Church numeral and a Church boolean?
\<lambda>s\<lambda>z.z

b) What problem do we solve by adding a type system to the lambda-calculus?

Lambda calculus cannot directly be used as an internal logical language via
church encodings, as there are divergent terms which satisfy equations
like T = not T. Adding a type system rules out these malformed terms in
a computable way.

c) Many basic operators of logic in Isabelle/HOL, such as \<forall> and \<and>, are
  derived operators rather than built-in operators. Why do you think that is?

This enables the trusted core of the logic to be as simple as possible,
so it is easier to verify its correctness.

d) What is the difference between \<forall> and \<And> in Isabelle?

The first forall is internal and is expressed as a proposition which may eval
true or false, the second symbol is a meta-statement of truth which
must be derived via the rules.

e) Why does Isabelle insist that recursive functions must terminate, when most programming languages
  don't?

Allowing divergent recursion can result in unsoundness, which would make the
theorem prover unhelpful for verification. An example is that if
f(x) does not terminate, f(x) = f(x) + 1 holds, but cancelling gives 0 = 1
which is false

f) What does it mean for a logic to be consistent?

False cannot be derived

g) Why is Hoare logic usually preferred over operational semantics for program verification?

Hoare logic is more convenient for reasoning about complex program
constructs in a way that is abstracted from the execution steps, avoiding
e.g. manual induction on every while loop. Weakest precondition generation
can be applied to automate generation of the proof goal.

h) What is the difference between an introduction rule and an elimination rule?

An intro rule describes how to construct a type/logical expression,
while an elim rule describes how to extract information by "destructing" it

i) What is the difference between a free variable and a schematic variable?

Schematic variables can be instantiated to any expression while retaining
truth, while free variables need to remain free (cannot be instantiated),
otherwise the statement may not hold in some contexts it should.

j) What is the difference between a deep embedding and a shallow embedding?

A shallow embedding represents only the semantics in an equivalent form,
while a deep embedding represents the syntax as a datatype which restricts the
well-formed "programs" to those of the language, so meta-results about the
embedded language can be proven. A semantics is then defined separately on
the syntax.

\<close>

(***********************)
(*     Question 2      *)
(***********************)

section \<open> Nothing, inductively (10 marks) \<close>

inductive_set nothing :: "'a set"
print_theorems

inductive_set also_nothing :: "'a set" where
 circ:  "x \<in> also_nothing \<Longrightarrow> x \<in> also_nothing"
print_theorems

lemma nothing_empty:
  "nothing = {}"
  unfolding nothing_def
  apply(simp add: nothingp.simps)
  done

lemma also_nothing_empty:
  "also_nothing = {}"
  apply(rule ccontr)
  apply(subgoal_tac "\<exists>x. x \<in> also_nothing")
   defer apply(force)
  apply(erule exE)
  apply(erule also_nothing.induct, assumption)
  done


(***********************)
(*     Question 3      *)
(***********************)

datatype arith =
  Var string
  | Num int
  | Add arith arith
  | Times arith arith

type_synonym env = "string \<Rightarrow> int"

primrec eval :: "env \<Rightarrow> arith \<Rightarrow> int" where
  "eval \<Gamma> (Var x) = \<Gamma> x"
| "eval \<Gamma> (Num i) = i"
| "eval \<Gamma> (Add e1 e2) = eval \<Gamma> e1 + eval \<Gamma> e2"
| "eval \<Gamma> (Times e1 e2) = eval \<Gamma> e1 * eval \<Gamma> e2"

fun simplify' :: "arith \<Rightarrow> arith" where
  "simplify'(Add (Num n) (Num m)) = Num(n+m)"
| "simplify'(Add e1 e2) = Add (simplify' e1) (simplify' e2)"
| "simplify'(Times (Num n) (Num m)) = Num(n*m)"
| "simplify'(Times e1 e2) = Times (simplify' e1) (simplify' e2)"
| "simplify' x = x"
print_theorems

thm simplify'.induct (* this theorem is your new best friend! *)

lemma simplify'_eval: "eval \<Gamma> (simplify' e) = eval \<Gamma> e"
  apply(induct rule: simplify'.induct;simp)
  done

lemma simplify'_not_idem:
  "\<exists>e. simplify'(simplify' e) \<noteq> simplify' e"
  apply(rule_tac x="Add (Num 0) (Add (Num 1) (Num 2))" in exI)
  apply(simp)
  done

lemma simplify'_size_le:
  "size_arith(simplify' e) \<le> size_arith e"
  apply(induct rule: simplify'.induct;simp)
  done

lemma simplify'_same_size_eq:
  "\<lbrakk>size_arith(simplify' e) = size_arith e\<rbrakk> \<Longrightarrow> simplify' e = e"
  apply(induct e;clarsimp)
   apply(case_tac "\<exists>n m. e1 = (Num n) \<and> e2 = (Num n)";clarsimp)
   apply(subgoal_tac "simplify'(Add e1 e2) = Add (simplify' e1) (simplify' e2)")
    apply(simp)
    apply(metis diff_diff_cancel diff_is_0_eq' diff_zero pl_pl_mm simplify'_size_le)
   apply(case_tac e1; case_tac e2; simp)
  apply(case_tac "\<exists>n m. e1 = (Num n) \<and> e2 = (Num n)";clarsimp)
  apply(subgoal_tac "simplify'(Times e1 e2) = Times (simplify' e1) (simplify' e2)")
   apply(simp)
   apply(metis diff_diff_cancel diff_is_0_eq' diff_zero pl_pl_mm simplify'_size_le)
  apply(case_tac e1; case_tac e2; simp)
  done

function simplify :: "arith \<Rightarrow> arith" where
  "simplify e =
   (if simplify' e = e then e
    else simplify(simplify' e))
  "
  by pat_completeness auto
termination
  apply(relation "measure size_arith")
   apply(simp)
  apply(simp)
  apply(metis le_neq_implies_less simplify'_same_size_eq simplify'_size_le)
  done
print_theorems

lemma simplify_idem:
  "simplify(simplify x) = simplify x"
  apply(subgoal_tac "simplify' (simplify x) = (simplify x)")
   apply(simp)
  apply(induct x rule: simplify.induct)
  apply(case_tac "simplify' e = e")
   apply(simp)
  apply(simp)
  done

(***********************)
(*     Question 4      *)
(***********************)

section \<open>C Verification\<close>

declare split_of_bool[split del]
declare sum_of_bool_eq[simp del]
  
external_file "exam.c"
install_C_file "exam.c"
autocorres [unsigned_word_abs=expF, ts_force nondet=expF] "exam.c"

context exam
begin

thm expF'_def

lemma expF_correct:
  "\<lbrace> \<lambda>_. x ^ n  < UINT_MAX \<rbrace> (expF' x n)
   \<lbrace> \<lambda>rv s. rv = x ^ n \<rbrace>"
  unfolding expF'_def
  apply(wp)
   apply(subst whileLoop_add_inv[where
        I="\<lambda>(n',x',y) s. n' > 0 \<and> y * x'^n' = x^n"])
   apply(wp)
    apply(auto split: prod.splits)
     apply(rename_tac n' x' y)
     apply (metis Suc_lessD Suc_pred bot_nat_0.not_eq_extremum diff_is_0_eq dvd_imp_mod_0 even_Suc mod_eq_self_iff_div_eq_0 not_less)
    apply(rename_tac n' x' y)
    apply(subgoal_tac "(x' * x') ^ ((n' - Suc 0) div 2) = x' ^ (n'-1)")
  apply(simp)
  apply (metis One_nat_def bot_nat_0.extremum_strict mult.assoc mult.commute power_eq_if)
     apply (metis One_nat_def dvd_minus_mod dvd_mult_div_cancel power2_eq_square power_mult)
   apply (metis Zero_not_Suc dvd_def nonzero_mult_div_cancel_left numeral_2_eq_2 power2_eq_square power_mult)
  by (metis Suc_lessI mult.commute power_Suc0_right)

end

end