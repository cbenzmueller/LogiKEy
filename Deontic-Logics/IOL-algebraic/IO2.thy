theory IO2
  imports IO_LogicalBase
begin

(******************************************************************************)
(* Output-2 in the “Applications” style                                       *)
(*                                                                            *)
(* Proposition 4.1(2): output-2 is the largest regular operator dominated     *)
(* by the base slanted operator.                                              *)
(******************************************************************************)

definition out2_admissible :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where
  "out2_admissible op \<equiv>
      regular_dia op
    \<and> (\<forall>\<phi>. op \<phi> \<^bold>\<le> (\<^bold>\<diamond> \<phi>))"

definition largest_out2 :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where
  "largest_out2 op \<equiv>
      out2_admissible op
    \<and> (\<forall>op1. out2_admissible op1 \<longrightarrow> (\<forall>\<phi>. op1 \<phi> \<^bold>\<le> op \<phi>))"

consts IO2 :: "\<tau> \<Rightarrow> \<tau>" ("\<^bold>\<diamond>\<^sup>2\<^sub>o")

axiomatization where
  ax_IO2: "largest_out2 (\<^bold>\<diamond>\<^sup>2\<^sub>o)"

lemma IO2_admissible: "out2_admissible (\<^bold>\<diamond>\<^sup>2\<^sub>o)"
  using ax_IO2 unfolding largest_out2_def by blast

lemma IO2_regular: "regular_dia (\<^bold>\<diamond>\<^sup>2\<^sub>o)"
  using IO2_admissible unfolding out2_admissible_def by blast

lemma IO2_mono: "monotone (\<^bold>\<diamond>\<^sup>2\<^sub>o)"
  using IO2_regular regular_dia_implies_mono by blast

lemma IO2_dom: "(\<^bold>\<diamond>\<^sup>2\<^sub>o \<phi>) \<^bold>\<le> (\<^bold>\<diamond> \<phi>)"
  using IO2_admissible unfolding out2_admissible_def by blast

lemma IO2_from_norm:
  assumes "\<alpha> \<^bold>\<preceq> \<beta>"
  shows "(\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha>) \<^bold>\<le> \<beta>"
  using IO2_dom assms slanted_from_norm by metis

lemma IO2top: "\<^bold>\<diamond>\<^sup>2\<^sub>o \<^bold>\<top> \<^bold>\<le> \<^bold>\<top>"
  by (simp add: settrue_def)

lemma IO2SI:
  "((\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<beta> \<^bold>\<le> \<alpha>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>2\<^sub>o \<beta> \<^bold>\<le> \<phi>)"
  using IO2_mono unfolding monotone_def by auto

lemma IO2WO:
  "((\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<phi> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<psi>)"
  by auto

lemma IO2AND:
  "((\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> (\<phi> \<^bold>\<and> \<psi>))"
  by (simp add: setand_def)

lemma IO2OR:
  "((\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>2\<^sub>o \<beta> \<^bold>\<le> \<phi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>2\<^sub>o (\<alpha> \<^bold>\<or> \<beta>) \<^bold>\<le> \<phi>)"
  using IO2_regular regular_dia_def setor_def by auto


end
