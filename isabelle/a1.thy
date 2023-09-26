theory a1
imports Main
begin


section "Q1: \<lambda>-Calculus"

(* a.
  x y (\<lambda>xyz. z (x y))
  using that lambdas bind as far as possible to the right and
  that lambda application is left associative.
*)

(* b.
  (x (\<lambda>x.(\<lambda>y.(x (y z)) (x y)))) (\<lambda>y. (y z))
*)

(* c.
(\<lambda>f. (\<lambda>x. (f (f (f x))))) (\<lambda>g. (\<lambda>y. (g (g y))))
-----------------------------------------------
\<lambda>x. ((\<lambda>g. (\<lambda>y. (g (g y)))) ((\<lambda>g. (\<lambda>y. (g (g y)))) ((\<lambda>g. (\<lambda>y. (g (g y)))) x)))
                                                  ---------------------------
\<lambda>x. ((\<lambda>g. (\<lambda>y. (g (g y)))) ((\<lambda>g. (\<lambda>y. (g (g y)))) (\<lambda>y. (x (x y)))))
                            ----------------------------------------
\<lambda>x. ((\<lambda>g. (\<lambda>y. (g (g y)))) (\<lambda>y. ((\<lambda>a. (x (x a))) ((\<lambda>a. (x (x a))) y))))
                                                  -------------------
\<lambda>x. ((\<lambda>g. (\<lambda>y. (g (g y)))) (\<lambda>y. ((\<lambda>a. (x (x a))) (x (x y)))))
                                ------------------------------
\<lambda>b. ((\<lambda>g. (\<lambda>y. (g (g y)))) (\<lambda>y. (b (b (b (b y))))))
     ----------------------------------------------     
\<lambda>b. (\<lambda>y. ((\<lambda>c. (b (b (b (b c))))) ((\<lambda>c. (b (b (b (b c))))) y)))
                                   ----------------------------
\<lambda>b. (\<lambda>y. ((\<lambda>c. (b (b (b (b c))))) (b (b (b (b y))))))
          --------------------------------------
\<lambda>s. (\<lambda>y. (s (s (s (s (s (s (s (s y)))))))))
*)

(* d.
  exp \<equiv> \<lambda>mn.n m
  (\<lambda>mn.n m) (\<lambda>fx. ff...fx) (\<lambda>f'x. f' f'... f'x)
\<rightarrow> (\<lambda>fx. ff...n times...fx) (\<lambda>f'x. f' f'...m times...f'x)
\<rightarrow> which passes (\<lambda>f'x. m applications of f' to x) to the next f,
   duplicating
*)

section "Q2: Types"

(* a. let \<Gamma> contain any undischarged variables before Abs
               ---------Var --------Var
               \<Gamma> \<turnstile> c :: B\<rightarrow>C  \<Gamma> \<turnstile> b :: B
    ---------Var    ------------App
   \<Gamma> \<turnstile> a :: C\<rightarrow>B\<rightarrow>X  \<Gamma> \<turnstile> c b :: C
    ---------------------App   ------------Var
    \<Gamma> \<turnstile> (a (c b)) :: B\<rightarrow>X       \<Gamma> \<turnstile> b :: B
    ----------------------------------App
    \<Gamma>[b <- B] \<turnstile> a (c b) b :: X
    ----------------------------------Abs
   \<Gamma>[a <- C\<rightarrow>B\<rightarrow>X] \<turnstile> \<lambda>b. a (c b) b :: B\<rightarrow>X 
    ---------------------------------Abs
   \<Gamma> \<turnstile> \<lambda>ab.a (c b) b : (C\<rightarrow>B\<rightarrow>X)\<rightarrow>B\<rightarrow>X

   This term is correct if the initial context contains
   [c <- B\<rightarrow>C]
*)

(* b.
  b : a \<rightarrow> b, c : a \<rightarrow> b \<rightarrow> c
  \<lambda>b.\<lambda>a.\<lambda>c. c a (b a)
*)

(* c.
  \<lambda>x.xx : \<alpha>
  the type must be obtained by the abs rule  \<Gamma>[x <- T] \<turnstile> x x :: T
  and x x :: T must have been obtained by the App rule  \<Gamma> \<turnstile> x :: T \<rightarrow> T, \<Gamma> \<turnstile> x :: T
  However then the type of x occurs in the type of x, failing the occurs check.
  Hence the term has no most general type and cannot be typed.
*)

(* d.
  (\<lambda>xy.y)(\<lambda>z.zz) \<mapsto>\<beta> \<lambda>y.y : a' \<Rightarrow> a'
*)

(* e.
  (\<lambda>xy.y)(\<lambda>z.zz) is not typable as the second term isn't typable by c)
  Whatever type it has would be preserved under reduction so it'd have
  the same type of \<lambda>x.x: a' \<Rightarrow> a' by subject reduction, but the static rules
  exclude the derivation in the first place.
*)

section "Q3: Propositional Logic"

(*
You must use only these proof methods:
  - rule, erule, assumption, cases, frule, drule,
    rule_tac, erule_tac, frule_tac, drule_tac, rename_tac, case_tac

You must use only these proof rules:
   - impI, impE, conjI, conjE, disjI1, disjI2, disjE, notI, notE
     iffI, iffE, iffD1, iffD2, ccontr, classical, FalseE,
     TrueI, conjunct1, conjunct2, mp
*)

lemma prop_a: "A \<longrightarrow> \<not>\<not>A"
  apply(rule impI)
  apply(rule notI)
  apply(erule notE)
  apply assumption
  done

lemma prop_b: "\<not>\<not>\<not> A \<longrightarrow> \<not>A"
  apply(rule impI)
  apply(rule notI)
  apply(erule notE)
  apply(rule impE[where P = A and Q = "\<not>\<not>A"])
  apply(rule prop_a)
   apply assumption
  apply assumption
  done

lemma prop_c: "\<not>\<not> A \<longrightarrow> A"
  apply(rule impI)
  apply(cases A)
   apply assumption
  apply(erule notE)
  apply assumption
  done

lemma prop_d:  "\<not>(A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
  apply(rule impI)
  apply(cases A)
   apply(rule disjI2)
   apply(rule notI)
   apply(drule conjI[where P = A and Q = B])
    apply assumption
   apply(erule notE)
   apply assumption
  apply(rule disjI1)
  apply assumption
  done

lemma prop_e:  "(A \<longrightarrow> B) \<longrightarrow> (\<not> A \<or> B)"
  apply(rule impI)
  apply(cases A)
   apply(drule mp)
  apply assumption
   apply(rule disjI2)
   apply assumption
  apply(rule disjI1)
  apply assumption
  done

lemma prop_f:  "\<not>A\<and>\<not>B \<longleftrightarrow> \<not>(A\<or>B)"
  apply(rule iffI)
   apply(rule notI)
   apply(erule disjE)
    apply(drule conjunct1)
    apply(erule notE)
    apply assumption
   apply(drule conjunct2)
  apply(erule notE)
   apply assumption
  apply(rule conjI)
   apply(rule notI)
   apply(erule notE)
   apply(rule disjI1)
   apply assumption
  apply(rule notI)
  apply(erule notE)
  apply(rule disjI2)
  apply assumption
  done

lemma prop_e_imp:  "(A \<longrightarrow> B) \<Longrightarrow> (\<not> A \<or> B)"
  apply(cases A)
   apply(drule mp)
  apply assumption
   apply(rule disjI2)
   apply assumption
  apply(rule disjI1)
  apply assumption
  done

lemma prop_e_inv: "(\<not> A \<or> B) \<Longrightarrow> (A \<longrightarrow> B)"
  apply(rule impI)
  apply(erule disjE)
   apply(erule notE)
   apply assumption
  apply assumption
  done

lemma prop_c_imp: "\<not>\<not> A \<Longrightarrow> A"
  apply(cases A)
   apply assumption
  apply(erule notE)
  apply assumption
  done

lemma contrapos: "(\<not>B \<longrightarrow> \<not>A) \<Longrightarrow> A \<longrightarrow> B"
  apply(rule prop_e_inv)
  apply(drule prop_e_imp)
  apply(erule disjE)
   apply(drule prop_c_imp)
   apply(rule disjI2)
   apply assumption
  apply(rule disjI1)
  apply assumption
  done

lemma prop_g_lem: "((B \<longrightarrow> C) \<longrightarrow> A) \<Longrightarrow> \<not>A \<Longrightarrow> B"
  apply(drule prop_e_imp)
  apply(erule disjE)
  apply(rule impE[where P = "\<not>(B \<longrightarrow> C)" and Q = B])
     apply(rule contrapos)
  apply(rule impI)
     apply(rule impE[where P = "B \<longrightarrow> C" and Q = "\<not>\<not>(B \<longrightarrow> C)"])
       apply(rule prop_a)
      apply(rule prop_e_inv)
      apply(rule disjI1)
      apply assumption
     apply assumption
    apply assumption
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma prop_g: "(A \<longrightarrow> B) \<longrightarrow> (((B \<longrightarrow> C) \<longrightarrow> A) \<longrightarrow> B)"
  apply(rule impI)
  apply(rule impI)
  apply(cases A)
   apply(erule mp)
   apply assumption
  apply(rule prop_g_lem)
   apply assumption
  apply assumption
  done

section "Q4: Higher-Order Logic"

(*
You must use only these proof methods:
  - rule, erule, assumption, frule, drule,
    rule_tac, erule_tac, frule_tac, drule_tac, rename_tac, case_tac
You must use only these proof rules:
   - impI, impE, conjI, conjE, disjI1, disjI2, disjE, notI, notE
     iffI, iffE, iffD1, iffD2, ccontr, classical, FalseE,
     TrueI, conjunct1, conjunct2, mp;
   - allI, allE, exI, and exE
*)

lemma hol_a: "(\<exists>x. P x \<longrightarrow> Q) \<longrightarrow> (\<forall>x. P x) \<longrightarrow> Q"
  apply(rule impI)
  apply(rule impI)
  apply(erule exE)
  apply(erule allE)
  apply(erule mp)
  apply assumption
  done

lemma hol_b: "((\<exists>x. P x) \<longrightarrow> Q) \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Q)"
  apply(rule iffI)
   apply(rule allI)
   apply(rule impI)
   apply(erule impE)
    apply(rule exI)
    apply assumption
   apply assumption
  apply(rule impI)
  apply(erule exE)
  apply(erule allE)
  apply(erule mp)
  apply assumption
  done

lemma hol_c_lem: "\<nexists>x. \<not> P x \<Longrightarrow> \<forall>x. P x"
  apply(rule allI)
  apply(rule ccontr)
  apply(erule notE)
  apply(rule exI)
  apply assumption
  done

lemma hol_c: "(\<forall>x. P x) \<longleftrightarrow> \<not> (\<exists>x. \<not> P x)"
  apply(rule iffI)
   apply(rule notI)
   apply(erule exE)
   apply(erule allE)
   apply(erule notE)
   apply assumption
  apply(rule hol_c_lem)
  apply assumption
  done

lemma hol_d: "(\<forall>x. P x \<and> Q x) \<longrightarrow> (\<forall>x. P x) \<and> (\<forall>x. Q x)"
  apply(rule impI)
  apply(rule conjI)
   apply(rule allI)
   apply(erule allE)
   apply(drule conjunct1)
   apply assumption
  apply(rule allI)
  apply(erule allE)
  apply(drule conjunct2)
  apply assumption
  done

lemma hol_e: "(\<exists>x. P x \<or> Q x) \<longrightarrow> (\<exists>x. P x) \<or> (\<exists>x. Q x)"
  apply(rule impI)
  apply(erule exE)
  apply(erule disjE)
   apply(rule disjI1)
   apply(rule exI)
   apply assumption
  apply(rule disjI2)
  apply(rule exI)
  apply assumption
  done

lemma prop_f_inv: "\<not>(A\<or>B) \<Longrightarrow> \<not>A \<and> \<not>B"
  apply(rule conjI)
   apply(rule notI)
   apply(erule notE)
   apply(rule disjI1)
   apply assumption
  apply(rule notI)
  apply(erule notE)
  apply(rule disjI2)
  apply assumption
  done

text \<open> this is just contrapositive of hol_c \<close>
lemma hol_c_neg: "\<not>(\<forall>x. P x) \<Longrightarrow> \<exists>x. \<not>P x"
  apply(rule ccontr)
  apply(erule notE)
  apply(rule hol_c_lem)
  apply assumption
  done

lemma hol_f: "(\<forall>x y. A y \<or> B x) \<longrightarrow> (\<forall>x. B x) \<or> (\<forall>y. A y)" 
  apply(rule contrapos)
  apply(rule impI)
  apply(rule notI)
  apply(drule prop_f_inv)
  apply(erule conjE)
  apply(erule notE)
  apply(rule allI)
  apply(drule hol_c_neg)
  apply(erule exE)
  apply(erule allE)
  apply(erule allE)
  apply(erule disjE)
   apply(erule notE)
   apply assumption
  apply assumption
  done

end