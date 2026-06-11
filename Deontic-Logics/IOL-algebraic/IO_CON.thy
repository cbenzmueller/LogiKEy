theory IO_CON
  imports IO_LogicalBase
begin

(* -------------------------------------------------------------------------- *)
(* Shared constrained-I/O layer                                                *)
(* -------------------------------------------------------------------------- *)

type_synonym normsys = "\<tau> \<Rightarrow> \<tau> \<Rightarrow> bool"

abbreviation (input) normsubset :: "normsys \<Rightarrow> normsys \<Rightarrow> bool" (infix "\<^bold>\<sqsubseteq>" 53)
  where "N1 \<^bold>\<sqsubseteq> N2 \<equiv> \<forall>a b. N1 a b \<longrightarrow> N2 a b"

definition slantedN :: "normsys \<Rightarrow> \<tau> \<Rightarrow> \<tau>"
  where "slantedN N \<phi> \<equiv> \<^bold>\<And>(\<lambda>x. N \<phi> x)"

notation slantedN ("\<^bold>\<diamond>\<^sub>c")

lemma slantedN_from_norm:
  assumes "N \<alpha> \<beta>"
  shows "slantedN N \<alpha> \<^bold>\<le> \<beta>"
  using assms unfolding slantedN_def infimum_def by auto

end
