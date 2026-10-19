theory Ref imports Main
begin

(* induction examples *)

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
  apply(simp) (* RHS = itrev [a] xs *)
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

(* conditional insertion sorting, unsolved by hipster *)
primrec insort' :: "'a::ord \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort' x [] = [x]" |
  "insort' x (y#ys) =
  (if x \<le> y then (x#y#ys) else y#(insort' x ys))"

definition sort' :: "('a::ord) list \<Rightarrow> 'a list" where
  "sort' xs = fold insort' xs []"

lemma count_insort':
  "count_list (insort' a as) n
 = (if n = a then Suc (count_list as n) else count_list as n)"
  apply(induct as, simp)
  apply(cases "n = a"; case_tac "aa=n")
     apply(simp)
    apply(simp only: refl if_True if_False count_list.simps insort'.simps)
    apply(case_tac "a \<le> aa"; simp only: if_True)
     apply(simp, simp)
   apply(simp only: refl if_True if_False count_list.simps insort'.simps)
   apply(case_tac "a \<le> n"; simp only: if_True if_False)
    apply(simp, simp)
  apply(simp only: if_False insort'.simps)
  apply(case_tac "a \<le> aa"; simp only: if_True if_False)
  apply(simp,simp)
  done

(* CLAM version *)
primrec isort :: "('a::ord) list \<Rightarrow> 'a list" where
  "isort [] = []" |
  "isort (a#as) = insort' a (isort as)"

lemma "count_list as n = count_list (isort as) n"
  apply(induct as, simp)
  apply(simp del: count_list.simps)
  apply(simp add: count_insort')
  by fastforce

(* harder foldl version from Isabelle requiring commutativity *)
lemma insort'_commute:
  "insort' (a::nat) (insort' n xs) = insort' n (insort' a xs)"
  apply(induct xs arbitrary: a n, simp)
  apply(case_tac "n \<le> a"; case_tac "aa \<le> a"; simp only: if_True if_False insort'.simps)
    apply(case_tac "aa \<le> n"; case_tac "n \<le> aa"; simp only: if_True if_False)
  using le_antisym apply fastforce
   apply(case_tac "aa \<le> n"; simp only: if_False)
  apply(case_tac "n \<le> aa"; simp only: if_False)
  done

lemma fold_insort'_insort':
  "fold insort' xs (insort' (n :: nat) ys)
 = insort' n (fold insort' xs ys)"
  apply(induct xs arbitrary: ys n, simp)
  apply(simp)
  apply(rule insort'_commute)
  done

lemma "count_list as (n :: nat) = count_list (sort' as) n"
  apply(simp add: sort'_def)
  apply(induct as, simp)
  apply(simp del: count_list.simps)
  apply(simp only: insort'.simps[symmetric])
  apply(subst fold_insort'_insort')
  apply(case_tac "a=n"; simp only: refl if_True if_False count_list.simps)
   apply(simp add: count_insort')
  apply(simp add: count_insort')
  done

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
  apply(auto simp add: lplus_assoc)
   apply(rule distrib_right)
  apply(rule_tac f="map2 (+) (xs ⊛ (y # ys))" in arg_cong)
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
  apply(simp only:) (* apply IH *)
  apply(rule_tac f="map2 (+) (as ⊛ ((b # bs) ⊛ (c # cs)))"
                 in arg_cong)
  apply(subst convol_linear)
  using lplus_linear
  apply(metis (no_types) ext comp_apply map_map mult.assoc)
  done

end