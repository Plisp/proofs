theory Ref imports Main
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

(*
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

text \<open> use SOME to delay choice for later instantiation \<close>
lemma choice:
  "\<forall>x. \<exists>y. R x y \<Longrightarrow> \<exists>f. \<forall>x. R x (f x)"
  apply(rule exI[where x="\<lambda>x. SOME y. R x y"])
  apply(rule allI)
  apply(erule allE)
  apply(erule exE)
  thm someI
  apply(rule someI)
  apply(assumption)
  done

(* blue variables: top-level free variables from the goal statement *)
(* green variables: bound variables *)
(* orange variables: free variables from a local proof context *)
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
(* no_asm_simp, no_asm_use *)
lemma "True \<and> ((\<exists>u::nat. x=y+u) \<longrightarrow> a*(b+c)+y \<le> x + a*b+a*c)"
  apply(auto)[1]
  apply(simp (no_asm) add: add_mult_distrib2 split: nat.split)
  done

declare [[simp_trace=false]]

(* [intro/elim/dest like conjunct1] *)
(* [cong] PQ = P' Q' by lifting P = Q*)
(* [simp] for rules *)
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

(* inductive sets *)
inductive_set Fin :: "'a set set" where
  emptyI[simp]: "{} \<in> Fin" | (* add simp *)
  insertI: "A \<in> Fin \<Longrightarrow> insert a A \<in> Fin"
print_theorems

declare Fin.intros[intro]
thm Fin.intros
lemma "\<lbrakk> A \<in> Fin ; B \<in> Fin \<rbrakk> \<Longrightarrow> A \<union> B \<in> Fin"
  apply(erule Fin.induct)
   apply simp
  apply auto
  done

lemma "\<lbrakk> A \<in> Fin ; B \<subseteq> A \<rbrakk> \<Longrightarrow> B \<in> Fin"
  apply(erule Fin.induct)
  oops

(* want to induct on A instead *)
lemma "A \<in> Fin \<Longrightarrow> B \<subseteq> A \<longrightarrow> B \<in> Fin"
  apply(erule Fin.induct)
   apply auto[1]
  apply(clarsimp del: subsetI)
  oops

(* strengthen IH *)
lemma "A \<in> Fin \<Longrightarrow> \<forall>B. B \<subseteq> A \<longrightarrow> B \<in> Fin"
  apply(erule Fin.induct)
   apply(simp, clarify)
  thm insert_Diff subset_insert_iff
  apply(simp add: subset_insert_iff)
  apply(simp split: if_split_asm) (* B - {a} case *)
  apply(drule_tac A=B in insert_Diff)
  apply(erule subst) (* B - {a} matches asm *)
  apply(blast)
  done

(* fixpoint exercise unfolding *)
definition
  closed :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "closed f B \<equiv> f B \<subseteq> B"

definition
  lfpt :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "lfpt f \<equiv> \<Inter> {B. closed f B}"

lemma lfpt_lower: "closed f B \<Longrightarrow> lfpt f \<subseteq> B"
  apply(unfold closed_def lfpt_def)
  apply fast
  done

lemma lfpt_fixpoint1:
  "mono f \<Longrightarrow> f (lfpt f) \<subseteq> lfpt f"
  apply(unfold lfpt_def)
  apply(clarify) (* take any prefixed (closed) point, prove f(lfpt) is smaller *)
  apply(frule lfpt_lower) (* lfp=meet is a lower bound (smaller than any prefixed set X) *)
  apply(unfold mono_def)
  apply(erule allE[where x="lfpt f"])
  apply(erule_tac x="X" in allE)
  apply(drule mp, assumption) (* f lfpt \<le> f X by monotonicity, but lfp is the greatest such set *)
  apply(auto simp add: lfpt_def closed_def) (* done, but sets *)
  done

lemma lfpt_fixpoint2:
  "mono f \<Longrightarrow> lfpt f \<subseteq> f(lfpt f)"
  apply(insert lfpt_fixpoint1[where f=f])
  apply(simp) (* can substitute frule mp *)
  apply(unfold mono_def)
  apply(erule allE[where x="f (lfpt f)"]) (* F lfpt is pre-fixed by monotonicity *)
  apply(erule allE[where x="lfpt f"])
  apply(simp)
  thm lfpt_lower
  apply(insert lfpt_lower[where f=f and B="f (lfpt f)"]) (* pre-fixed points smaller than lfp*)
  apply(simp add: closed_def)
  done

lemma lfpt_fixpoint:
  "mono f \<Longrightarrow> f (lfpt f) = lfpt f"
  apply (rule equalityI)
   apply (erule lfpt_fixpoint1, erule lfpt_fixpoint2)
  done

lemma lfpt_least:
  "f A = A \<Longrightarrow> lfpt f \<subseteq> A"
  apply(rule_tac B=A in lfpt_lower)
  apply(simp add:closed_def)
  done

consts R :: "('a set \<times> 'a) set"
definition
  R_hat :: "'a set \<Rightarrow> 'a set" where
  "R_hat A \<equiv> {x. \<exists>H. (H, x) \<in> R \<and> H \<subseteq> A}"

lemma monoR': "mono R_hat"
  apply (unfold mono_def)
  apply (unfold R_hat_def)
  apply blast
  done

lemma sound:
  assumes hyp: "\<forall>(H,x) \<in> R. (\<forall>h \<in> H. P h) \<longrightarrow> P x"
  shows "\<forall>x \<in> lfpt R_hat. P x"
proof -
  from hyp
  have "closed R_hat {x. P x}"
    unfolding closed_def R_hat_def by blast
  hence "lfpt R_hat \<subseteq> {x. P x}"
    by (simp add: lfpt_lower)
  thus ?thesis
    by fast
qed

lemma test:
  "(\<forall>x. P(x)) \<Longrightarrow> \<exists>x. P(x)"
  by fast

(* inductive types *)
datatype 'a mylist = MyNil | MyCons 'a "'a mylist"
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

(* mutually recursive types *)
datatype
  ty = Integer | Real | RefT ref
  and
  ref = Class | Array ty

term "MyCons (1::nat) MyNil"
thm mylist.distinct mylist.inject
(* string = char list, char = bool \<times> bool \<times> bool \<times> bool \<times> bool \<times> bool \<times> bool \<times> bool *)
thm char.split_asm

(* case split on variants *)
lemma "length xs = length xs"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

text \<open> partial cases and dummy patterns: \<close>
term "case t of Node _ b _ => b"
text \<open> partial case maps to 'undefined': \<close>
lemma "(case Tip of Node _ _ _ => 0) = undefined" by simp
text \<open> nested case and default pattern: \<close>
term "case t of Node (Node _ _ _) x Tip => 0 | _ => 1"
*)

(* induction examples *)

(* lists as maps to sets? *)
type_synonym 'a mylist = "nat \<times> ('a \<Rightarrow> nat set)"
definition map_valid :: "'a mylist \<Rightarrow> bool" where
  "map_valid m \<longleftrightarrow>
     (\<forall>k. k < fst m \<longrightarrow> (\<exists>!e. k \<in> snd m e)) \<and>
     (\<forall>k i. i \<in> snd m k \<longrightarrow> i < fst m)"
definition list_map_rel :: "'a list \<Rightarrow> 'a mylist \<Rightarrow> bool" where
  "list_map_rel xs m \<longleftrightarrow>
     fst m = length xs \<and>
     (\<forall>x i. i \<in> snd m x \<longleftrightarrow> i < fst m \<and> xs ! i = x)"

definition map_append :: "'a mylist \<Rightarrow> 'a mylist \<Rightarrow> 'a mylist" where
  "map_append m1 m2 =
     (fst m1 + fst m2, (\<lambda>k. snd m1 k \<union> (\<lambda>i. fst m1 + i) ` (snd m2 k)))"

lemma map_append_rel:
  "list_map_rel xs m1 \<and> list_map_rel ys m2
  \<Longrightarrow> list_map_rel (xs @ ys) (map_append m1 m2)"
  unfolding map_append_def list_map_rel_def
  apply(simp)
  by (smt (verit, del_insts) add_diff_cancel_left' add_diff_inverse_nat
      image_iff le_eq_less_or_eq nat_add_left_cancel_less nat_le_linear
      not_add_less1 nth_append_left nth_append_right trans_less_add1)

definition map_reverse :: "'a mylist \<Rightarrow> 'a mylist" where
  "map_reverse m = (fst m, (\<lambda>k. (\<lambda>n. fst m - n - 1) ` (snd m k)))"

lemma map_reverse_rel:
  "list_map_rel xs m \<Longrightarrow> list_map_rel (rev xs) (map_reverse m)"
  unfolding map_reverse_def list_map_rel_def
  apply(induct xs, fastforce)
  apply(simp)
  sorry

lemma map_reverse_reverse:
  "map_valid m \<Longrightarrow> (map_reverse (map_reverse m)) = m"
  unfolding map_reverse_def map_valid_def
  apply(cases m)
  apply(simp add: ext set_eqI Suc_diff_Suc image_iff le_eq_less_or_eq)
  done

(* easy equational *)
fun halve :: "nat \<Rightarrow> nat"
where
  "halve 0 = 0" |
  "halve (Suc 0) = 0" |
  "halve (Suc (Suc n)) = Suc (halve n)"

lemma "halve (n + n) = n"
  apply(induct n, simp)
  apply(simp only: add_Suc_right add_Suc)
  apply(simp only: halve.simps)
  done

(* generalization *)
primrec itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"

lemma itrev_gen: "itrev xs ys = (rev xs) @ ys"
  apply(induct xs arbitrary: ys, simp)
  thm meta_spec (* very useful for instantiating big and *)
  apply(drule_tac x="a#ys" in meta_spec)
  apply(simp)
  done

lemma "itrev xs [] = rev xs" by (simp add: itrev_gen)

(* unsolved by cclemma, requires unevaluation *)
lemma "itrev (itrev xs []) Nil = xs" (* = itrev [] xs *)
  apply(induct xs, simp)
  apply(simp)
  oops

lemma itrevrev: "itrev (itrev xs ys) Nil = itrev ys xs"
  apply(induct xs arbitrary: ys, simp)
  apply(simp)
  done

(* harder version of benchmark problem, length is most obvious *)
fun evenl :: "nat list \<Rightarrow> bool"
  where
    "evenl [] = True" |
    "evenl [a] = False" |
    "evenl (_#_#as) = evenl as"
thm evenl.induct

lemma "evenl (l @ l)"
  apply(induct l, simp) (* not possible to case on l *)
  oops

lemma evenl1: "evenl (as @ l) \<Longrightarrow> evenl (as @ a#a'#l)"
  apply(induct as rule: evenl.induct)
    apply(simp)
   apply(simp)
   apply(case_tac l, simp, simp)
  apply(simp)
  done

lemma "evenl (l @ l)"
  apply(induct l rule: evenl.induct, simp, simp)
  apply(simp add: evenl1)
  done

(* difficult (without lemmas), unsolved by hipster *)
lemma "length (filter p xs) \<le> length xs"
  apply(induct xs, simp)
  apply(case_tac "p a")
   apply(simp only: list.size filter.simps)
   apply(subst if_True)
   apply(subst list.size(4))
   apply(subst add_Suc_right)+
  thm Suc_le_mono add_0_right (* needed *)
   apply(simp only: Suc_le_mono add_0_right)
  apply(simp only: list.size filter.simps)
  apply(subst if_False)
  apply(subgoal_tac "length xs \<le> length xs + Suc 0")
   apply linarith (* transitivity *)
  apply(rule le_add1)
  done

(* TODO conditional insertion sorting, unsolved by hipster *)
primrec count :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "count n [] = 0" |
  "count n (k#ks) = (if n = k then 1 else 0) + count n ks"

lemma "count n xs = count n (sort xs)"
  apply(simp add: List.linorder_class.sort_conv_fold)
  apply(induct xs, simp)
  apply(simp)
(* what is the benchmark definition?*)
  sorry

(* generalization from single variable *)
fun rot :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "rot 0 l = l" |
  "rot x [] = []" |
  "rot (Suc x) (b#bs) = rot x (bs @ [b])"

lemma rot_gen: "rot (length as) (as @ bs) = bs @ as"
  apply(induct as arbitrary: bs, simp) (* generalize *)
  apply(simp del: append_assoc)
  apply(simp (no_asm) only: append_assoc)
  (* induction with bs @ [a] *)
  apply(simp only:)
  apply(simp only: append_assoc)
  (* cong *)
  apply(metis Cons_eq_appendI eq_Nil_appendI)
  done

lemma "rot (length as) as = as"
  apply(induct as, simp)
  apply(simp)
  (* note a # as = [a] @ as *)
  apply(simp add: rot_gen)
  done

(* solved by hipster and not zeno, tricky single instance gen
   note: doesn't actually require the lemmas *)
lemma "take (length xs - i) (rev xs) = rev (drop i xs)"
  apply(induct xs arbitrary: i, simp)
  apply(simp del:take_append diff_is_0_eq' take_all drop_all)
  apply(case_tac i, simp)
  (* substitute i, reduce back to hyp.*)
  apply(simp only: diff_Suc_Suc, thin_tac "_ = _")
  apply(subgoal_tac "take (length xs - nat) (rev xs @ [a])
                   = rev (drop nat xs)", simp)
  (* extra @[a] in goal blocks unification *)
  sorry

lemma "take (length xs - i) (rev xs @ ys) = rev (drop i xs)"
  apply(induct xs arbitrary: i ys, simp)
  apply(simp del:take_append diff_is_0_eq' take_all drop_all append_assoc)
  apply(simp only: append_assoc) (* reasonable *)
  apply(case_tac i, simp, simp only:, thin_tac "_ = _")
  apply(simp (no_asm) only: diff_Suc_Suc) (* reasonable *)
  apply(simp only:) (* IH, absorb [a] @ ys *)
  apply(simp)
  done

(* convolution *)
fun convol :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
(infixl "⊛" 70) where
  "xs ⊛ [] = []" |
  "[] ⊛ ys = []" |
  "(x#xs)⊛(y#ys)
 = (x*y)#(map2 (+) (xs⊛(y#ys)) (map (\<lambda>y. x*y) ys))"

lemma lplus_linear:
  "map2 (+) (map ((*) (n :: nat)) as) (map ((*) n) bs)
 = map ((*) n) (map2 (+) as bs)"
  apply(induct as arbitrary: bs, simp)
  apply(case_tac bs; simp)
  apply(thin_tac "_")
  apply(rule distrib_left[symmetric])
  done

lemma lplus_assoc: "map2 (+) (map2 (+) (as :: nat list) bs) cs
                  = map2 (+) as (map2 (+) bs cs)"
  apply(induct as arbitrary: bs cs, simp)
  apply(case_tac bs; case_tac cs; simp)
  done

lemma lplus_comm: "map2 (+) (as :: nat list) bs = map2 (+) bs as"
  apply(induct as arbitrary: bs, simp)
  apply(case_tac bs; simp)
  done

lemma lplus_cancel:
   "map2 (+) (as :: nat list) bs = map2 (+) as cs
\<longleftrightarrow> take (length as) bs = take (length as) cs"
  apply(induct as arbitrary: bs cs, simp)
  apply(case_tac bs; case_tac cs; simp)
  done

lemma convol_nil: "[] ⊛ bs = map ((*) n) ([] ⊛ bs)"
  by(induct bs; simp)

lemma convol_linear:
  "(map ((*) n) as ⊛ bs) = (map ((*) n) (as ⊛ bs))"
  apply(induct as bs rule: convol.induct; simp)
  apply(subgoal_tac "map2 (+) (map ((*) n) (xs ⊛ (y # ys)))
        (map ((*) (n * x)) ys)
      = map2 (+) (map ((*) n) (xs ⊛ (y # ys)))
        (map ((*) n) (map ((*) x) ys))")
   defer
   apply(metis (no_types) ext comp_apply map_map mult.assoc)
  apply(simp only: lplus_linear)
  apply(simp only: map_map)
  done

lemma lplus_times_sum: "(map ((*) (x + a)) (ys :: nat list))
                      = map2 (+) (map ((*) x) ys) (map ((*) a) ys)"
  apply(induct ys, simp)
  apply(simp add: distrib_right)
  done

lemma convol_rdistrib: "(map2 (+) (as :: nat list) bs) ⊛ cs
                      = map2 (+) (as ⊛ cs) (bs ⊛ cs)"
  apply(induct as cs arbitrary: bs rule: convol.induct; simp)
  apply(case_tac bs; simp)
  apply(auto simp add: lplus_assoc lplus_cancel)
   apply(rule distrib_right)
  apply(rule_tac f="\<lambda>x. take (length (xs ⊛ (y # ys))) x" in arg_cong)
  using lplus_assoc lplus_comm lplus_times_sum
  apply(auto)
  done

lemma "(as ⊛ bs) ⊛ cs = as ⊛ (bs ⊛ cs)"
  apply(induct as arbitrary: bs cs)
   apply(case_tac bs; case_tac cs; simp)
  apply(case_tac bs; case_tac cs; simp)
  apply(thin_tac "_ = _")+
  apply(rename_tac a as bs' cs' b bs c cs)
  apply(subst convol.simps(3)[symmetric])
  apply(subst convol_rdistrib)
  apply(subst lplus_assoc)
  apply(simp add: lplus_cancel)
  apply(subgoal_tac " (map2 (+) (map ((*) a) bs ⊛ (c # cs))
                       (map ((*) (a * b)) cs))
                    = (map ((*) a \<circ> (\<lambda>(x, y). x + y))
                       (zip (bs ⊛ (c # cs)) (map ((*) b) cs)))")
   apply(simp)
  apply(subst convol_linear)
  using lplus_linear
  apply(metis (no_types) ext mult.assoc comp_def map_map)
  done

end