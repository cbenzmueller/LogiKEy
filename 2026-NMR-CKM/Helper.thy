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
    case (1 n P) then show ?case by simp
  next
    case (2 n P x xs i) then show ?case
      by (cases "P x") (auto simp: Suc_diff_Suc)
  qed

lemma find_index_pred_from_exists:
  assumes "∃x∈set xs. P x"
  shows "∃i. find_index_pred_from n P xs = Some i"
  using assms
  by (induction xs arbitrary: n) auto

lemma index_opt_SomeD:
  assumes "index_opt xs a = Some i"
  shows "i < length xs ∧ xs ! i = a"
  using find_index_pred_from_SomeD[of 0 "λx. x = a" xs i]
        assms unfolding index_opt_def find_index_pred_def
  by simp

lemma index_opt_mem:
  assumes "index_opt xs a = Some i"
  shows "a ∈ set xs"
  using index_opt_SomeD[OF assms] by (metis in_set_conv_nth)

lemma index_opt_exists_if_mem:
  assumes "a ∈ set xs"
  shows "∃i. index_opt xs a = Some i"
  using find_index_pred_from_exists[of xs "λx. x = a" 0] assms
  unfolding index_opt_def find_index_pred_def by auto

lemma find_index_mem_lt_length:
  assumes "a ∈ set xs"
  shows "find_index xs a < length xs"
  using index_opt_exists_if_mem[OF assms] index_opt_SomeD
  unfolding find_index_def by fastforce

lemma find_index_nth_if_mem:
  assumes "a ∈ set xs"
  shows "xs ! find_index xs a = a"
  using index_opt_exists_if_mem[OF assms] index_opt_SomeD
  unfolding find_index_def by fastforce

lemma split_by_find_index:
  assumes "a ∈ set xs"
  shows "xs = take (find_index xs a) xs @ a # drop (Suc (find_index xs a)) xs"
  using find_index_nth_if_mem[OF assms] find_index_mem_lt_length[OF assms]
  by (metis id_take_nth_drop)

lemma find_index_lt_length_if_mem:
  assumes "a ∈ set xs"
  shows "find_index xs a < length xs"
  using find_index_mem_lt_length[OF assms] .

lemma find_index_eq_length_if_not_mem:
  assumes "a ∉ set xs"
  shows "find_index xs a = length xs"
  using assms index_opt_mem unfolding find_index_def
  by force

lemma find_index_lt_length_imp_mem:
  assumes "find_index xs a < length xs"
  shows "a ∈ set xs"
  using assms find_index_eq_length_if_not_mem by force

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