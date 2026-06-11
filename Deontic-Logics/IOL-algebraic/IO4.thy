theory IO4
  imports IO_LogicalBase
begin

(******************************************************************************)
(* Output-4 in the “Applications” style                                       *)
(*                                                                            *)
(* Proposition 4.1(4): output-4 is the largest regular operator satisfying    *)
(* the CT-inequality and dominated by the base slanted operator.              *)
(******************************************************************************)

definition out4_admissible :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where
  "out4_admissible op \<equiv>
      regular_dia op
    \<and> (\<forall>\<phi>. op \<phi> \<^bold>\<le> op (\<phi> \<^bold>\<and> op \<phi>))
    \<and> (\<forall>\<phi>. op \<phi> \<^bold>\<le> (\<^bold>\<diamond> \<phi>))"

definition largest_out4 :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where
  "largest_out4 op \<equiv>
      out4_admissible op
    \<and> (\<forall>op1. out4_admissible op1 \<longrightarrow> (\<forall>\<phi>. op1 \<phi> \<^bold>\<le> op \<phi>))"

consts IO4 :: "\<tau> \<Rightarrow> \<tau>" ("\<^bold>\<diamond>\<^sup>4\<^sub>o")

axiomatization where
  ax_IO4: "largest_out4 (\<^bold>\<diamond>\<^sup>4\<^sub>o)"

lemma IO4_admissible: "out4_admissible (\<^bold>\<diamond>\<^sup>4\<^sub>o)"
  using ax_IO4 unfolding largest_out4_def by blast

lemma IO4_regular: "regular_dia (\<^bold>\<diamond>\<^sup>4\<^sub>o)"
  using IO4_admissible unfolding out4_admissible_def by blast

lemma IO4_mono: "monotone (\<^bold>\<diamond>\<^sup>4\<^sub>o)"
  using IO4_regular regular_dia_implies_mono by blast

lemma IO4_dom: "(\<^bold>\<diamond>\<^sup>4\<^sub>o \<phi>) \<^bold>\<le> (\<^bold>\<diamond> \<phi>)"
  using IO4_admissible unfolding out4_admissible_def by blast

lemma IO4_CTineq:
  "(\<^bold>\<diamond>\<^sup>4\<^sub>o \<phi>) \<^bold>\<le> (\<^bold>\<diamond>\<^sup>4\<^sub>o (\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>4\<^sub>o \<phi>))"
  using IO4_admissible unfolding out4_admissible_def by blast

lemma IO4_from_norm:
  assumes "\<alpha> \<^bold>\<preceq> \<beta>"
  shows "(\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha>) \<^bold>\<le> \<beta>"
  using IO4_dom assms slanted_from_norm by metis

lemma IO4top: "\<^bold>\<diamond>\<^sup>4\<^sub>o \<^bold>\<top> \<^bold>\<le> \<^bold>\<top>"
  by (simp add: settrue_def)

lemma IO4SI:
  "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<beta> \<^bold>\<le> \<alpha>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<beta> \<^bold>\<le> \<phi>)"
  using IO4_mono unfolding monotone_def by auto

lemma IO4WO:
  "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<phi> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<psi>)"
  by auto

lemma IO4AND:
  "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> (\<phi> \<^bold>\<and> \<psi>))"
  by (simp add: setand_def)

lemma IO4OR:
  "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<beta> \<^bold>\<le> \<phi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o (\<alpha> \<^bold>\<or> \<beta>) \<^bold>\<le> \<phi>)"
  using IO4_regular regular_dia_def setor_def by auto

lemma IO4CT:
  "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>4\<^sub>o (\<alpha> \<^bold>\<and> \<phi>) \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<psi>)"
  by (smt (verit, ccfv_threshold) IO4_CTineq IO4_mono IO_LogicalBase.monotone_def setand_def)

lemma IO4T:
  "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<phi> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<psi>)"
  by (smt (verit, ccfv_threshold) IO4_CTineq IO4_mono IO_LogicalBase.monotone_def setand_def)


end
