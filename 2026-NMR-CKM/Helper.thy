(* Luca Pasetto, Roberts Tarvids, Apostolos Tzimoulis and Christoph Benzmüller, 2026 *)
theory Helper
  imports Main
begin

nitpick_params[user_axioms=true, assms=true, expect=genuine, show_all, format=2]

fun find_index_pred_from :: "nat ⇒ ('a ⇒ bool) ⇒ 'a list ⇒ nat option" where
  "find_index_pred_from n P [] = None" |
  "find_index_pred_from n P (x # xs) =
     (if P x then Some n else find_index_pred_from (Suc n) P xs)"

definition find_index_pred :: "('a ⇒ bool) ⇒ 'a list ⇒ nat option" where
  "find_index_pred P xs = find_index_pred_from 0 P xs"

definition index_opt :: "'a list ⇒ 'a ⇒ nat option" where
  "index_opt xs a = find_index_pred (λx. x = a) xs"

definition find_index :: "'a list ⇒ 'a ⇒ nat" where
  "find_index xs a = (case index_opt xs a of Some i ⇒ i | None ⇒ length xs)"

lemma find_index_pred_from_SomeD:
  assumes "find_index_pred_from n P xs = Some i"
  shows "i ≥ n ∧ i - n < length xs ∧ P (xs ! (i - n))"
  using assms 
proof (induction n P xs arbitrary: i rule: find_index_pred_from.induct)
  case (1 n P)
  then show ?case by simp
next
  case (2 n P x xs i)
  show ?case 
  proof (cases "P x")
    case True
    with 2 show ?thesis by simp
  next
    case False 
    from 2 False obtain A B C where
      A: "i ≥ Suc n" and B: "i - Suc n < length xs" and C: "P (xs ! (i - Suc n))"
      by auto
    have "i ≥ n"
      using A by arith
    moreover have "i - n < length (x # xs)"
      using A B by simp
    moreover have "P ((x # xs) ! (i - n))"
    proof -
      have "i - n = Suc (i - Suc n)"
        using A by arith
      then show ?thesis
        using C by simp
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma find_index_pred_from_exists:
  assumes "∃x∈set xs. P x"
  shows "∃i. find_index_pred_from n P xs = Some i"
  using assms
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "P a")
    case True
    then show ?thesis by simp
  next
    case False
    have "∃x∈set xs. P x"
      using Cons.prems False by auto
    then obtain i where "find_index_pred_from (Suc n) P xs = Some i"
      using Cons.IH by blast
    then show ?thesis
      using False by simp
  qed
qed

lemma index_opt_SomeD:
  assumes "index_opt xs a = Some i"
  shows "i < length xs ∧ xs ! i = a"
proof -
  have "find_index_pred_from 0 (λx. x = a) xs = Some i"
    using assms unfolding index_opt_def find_index_pred_def by simp
  from find_index_pred_from_SomeD[OF this]
  have "i ≥ 0" and "i - 0 < length xs" and "(λx. x = a) (xs ! (i - 0))"
    by blast+
  then show ?thesis
    by simp
qed

lemma index_opt_mem:
  assumes "index_opt xs a = Some i"
  shows "a ∈ set xs"
  using index_opt_SomeD[OF assms]
  by (metis in_set_conv_nth)

lemma index_opt_exists_if_mem:
  assumes "a ∈ set xs"
  shows "∃i. index_opt xs a = Some i"
  using find_index_pred_from_exists[of xs "λx. x = a" 0] assms
  unfolding index_opt_def find_index_pred_def
  by auto

lemma find_index_mem_lt_length:
  assumes "a ∈ set xs"
  shows "find_index xs a < length xs"
proof -
  obtain i where I: "index_opt xs a = Some i"
    using index_opt_exists_if_mem[OF assms] by blast
  have "i < length xs"
    using index_opt_SomeD[OF I] by simp
  moreover have "find_index xs a = i"
    using I unfolding find_index_def by simp
  ultimately show ?thesis by simp
qed

lemma find_index_nth_if_mem:
  assumes mem: "a ∈ set xs"
  shows "xs ! find_index xs a = a"
proof -
  obtain i where I: "index_opt xs a = Some i"
    using index_opt_exists_if_mem[OF mem] by blast
  have nth: "xs ! i = a"
    using index_opt_SomeD[OF I] by simp
  have idx: "find_index xs a = i"
    using I unfolding find_index_def by simp
  show ?thesis
    using nth idx by simp
qed

lemma split_by_find_index:
  assumes mem: "a ∈ set xs"
  defines "n ≡ find_index xs a"
  shows "xs = take n xs @ a # drop (Suc n) xs"
proof -
  have nth: "xs ! n = a"
    using find_index_nth_if_mem[OF mem] n_def by simp
  then show ?thesis
    by (metis id_take_nth_drop find_index_mem_lt_length mem n_def)
qed

lemma find_index_lt_length_if_mem:
  assumes "a ∈ set xs"
  shows "find_index xs a < length xs"
  using find_index_mem_lt_length[OF assms] .

lemma find_index_eq_length_if_not_mem:
  assumes "a ∉ set xs"
  shows "find_index xs a = length xs"
proof -
  have "index_opt xs a = None"
  proof (rule ccontr)
    assume "index_opt xs a ≠ None"
    then obtain i where "index_opt xs a = Some i"
      by (cases "index_opt xs a") auto
    then have "a ∈ set xs"
      by (rule index_opt_mem)
    with assms show False by contradiction
  qed
  then show ?thesis
    unfolding find_index_def by simp
qed

lemma find_index_lt_length_imp_mem:
  assumes "find_index xs a < length xs"
  shows "a ∈ set xs"
proof (rule ccontr)
  assume "a ∉ set xs"
  then have "find_index xs a = length xs"
    by (rule find_index_eq_length_if_not_mem)
  with assms show False by simp
qed

definition fun_upd2 ::
  "('a ⇒ 'b ⇒ 'c) ⇒ 'a ⇒ 'b ⇒ 'c ⇒ ('a ⇒ 'b ⇒ 'c)" where
  "fun_upd2 Z x w i ≡ λy w1. if x = y ∧ w = w1 then i else Z y w1"

lemma fun_upd2_same [simp]:
  "fun_upd2 Z x w i x w = i"
  unfolding fun_upd2_def by simp

lemma fun_upd2_other [simp]:
  assumes "(x, w) ≠ (y, w1)"
  shows "fun_upd2 Z x w i y w1 = Z y w1"
  using assms unfolding fun_upd2_def by auto

end
