theory Scratch imports Main begin

term "x"
term "\<lambda>x. x"
term "Suc 5"

declare[[show_types=false]]

lemma ext_imp:
  "(x::int) > 0 \<and> y > 0 \<longrightarrow> x+y > 0"
  apply(rule impI)
  apply(simp)
  done  

lemma "B \<and> A \<longrightarrow> A \<and> B"
  apply(rule impI)
  apply(rule conjI)
   apply(erule conjE)
   apply(assumption)
    apply(erule conjE)
    apply(assumption)

lemma "A \<or> B \<longrightarrow> B \<or> A"
  apply(rule impI)
  apply(erule disjE)
   apply(rule disjI2)
   apply(assumption)
    apply(rule disjI1)
    apply(assumption)

text \<open> TODO how to \<forall>?, how to complete lambda faster \<close>
lemma alpha:
  "\<forall>t. (\<lambda>x. x) t = (\<lambda>y. y) t"
  apply(rule allE)
  apply(rule refl)

find_theorems "_ = _ \<equiv>_ x = _ x"
find_theorems "(_ + _) + _ = _ + (_ + _)"

end