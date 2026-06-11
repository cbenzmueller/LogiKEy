theory IO1
  imports IO_LogicalBase
begin

(******************************************************************************)
(* Output-1 in the “Applications” style                                       *)
(*                                                                            *)
(* Proposition 4.1(1): output-1 is the largest monotone operator dominated    *)
(* by the base slanted operator.                                              *)
(******************************************************************************)

definition out1_admissible :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where
  "out1_admissible op \<equiv>
      monotone op
    \<and> (\<forall>\<phi>. op \<phi> \<^bold>\<le> (\<^bold>\<diamond> \<phi>))"

definition largest_out1 :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where
  "largest_out1 op \<equiv>
      out1_admissible op
    \<and> (\<forall>op1. out1_admissible op1 \<longrightarrow> (\<forall>\<phi>. op1 \<phi> \<^bold>\<le> op \<phi>))"

consts IO1 :: "\<tau> \<Rightarrow> \<tau>" ("\<^bold>\<diamond>\<^sup>1\<^sub>o")

axiomatization where
  ax_IO1: "largest_out1 (\<^bold>\<diamond>\<^sup>1\<^sub>o)"

lemma IO1_admissible: "out1_admissible (\<^bold>\<diamond>\<^sup>1\<^sub>o)"
  using ax_IO1 unfolding largest_out1_def by blast

lemma IO1_mono: "monotone (\<^bold>\<diamond>\<^sup>1\<^sub>o)"
  using IO1_admissible unfolding out1_admissible_def by blast

lemma IO1_dom: "(\<^bold>\<diamond>\<^sup>1\<^sub>o \<phi>) \<^bold>\<le> (\<^bold>\<diamond> \<phi>)"
  using IO1_admissible unfolding out1_admissible_def by blast

lemma IO1_from_norm:
  assumes "\<alpha> \<^bold>\<preceq> \<beta>"
  shows "(\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha>) \<^bold>\<le> \<beta>"
  using IO1_dom assms slanted_from_norm 
  by metis

lemma IO1top: "\<^bold>\<diamond>\<^sup>1\<^sub>o \<^bold>\<top> \<^bold>\<le> \<^bold>\<top>"
  by (simp add: settrue_def)

lemma IO1SI:
  "((\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<beta> \<^bold>\<le> \<alpha>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>1\<^sub>o \<beta> \<^bold>\<le> \<phi>)"
  using IO1_mono unfolding monotone_def by auto

lemma IO1WO:
  "((\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<phi> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<psi>)"
  by auto

lemma IO1AND:
  "((\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> (\<phi> \<^bold>\<and> \<psi>))"
  by (simp add: setand_def)

lemma IO2OR:
  "((\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>1\<^sub>o \<beta> \<^bold>\<le> \<phi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>1\<^sub>o (\<alpha> \<^bold>\<or> \<beta>) \<^bold>\<le> \<phi>)"
  (* nitpick *)
  oops

end
