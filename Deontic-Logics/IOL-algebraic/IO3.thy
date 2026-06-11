theory IO3
  imports IO_LogicalBase
begin

(******************************************************************************)
(* Proposition 4.1(3): output-3 is the largest monotone operator satisfying   *)
(* the CT-inequality and dominated by the base slanted operator.              *)
(******************************************************************************)

definition out3_admissible :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where
  "out3_admissible op \<equiv>
      monotone op
    \<and> (\<forall>\<phi>. op \<phi> \<^bold>\<le> op (\<phi> \<^bold>\<and> op \<phi>))
    \<and> (\<forall>\<phi>. op \<phi> \<^bold>\<le> (\<^bold>\<diamond> \<phi>))"

definition largest_out3 :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where
  "largest_out3 op \<equiv>
      out3_admissible op
    \<and> (\<forall>op1. out3_admissible op1 \<longrightarrow> (\<forall>\<phi>. op1 \<phi> \<^bold>\<le> op \<phi>))"

consts IO3 :: "\<tau> \<Rightarrow> \<tau>" ("\<^bold>\<diamond>\<^sup>3\<^sub>o")

axiomatization where
  ax_IO3: "largest_out3 (\<^bold>\<diamond>\<^sup>3\<^sub>o)"

lemma IO3_admissible: "out3_admissible (\<^bold>\<diamond>\<^sup>3\<^sub>o)"
  using ax_IO3 unfolding largest_out3_def by blast

lemma IO3_mono: "monotone (\<^bold>\<diamond>\<^sup>3\<^sub>o)"
  using IO3_admissible unfolding out3_admissible_def by blast

lemma IO3_dom: "(\<^bold>\<diamond>\<^sup>3\<^sub>o \<phi>) \<^bold>\<le> (\<^bold>\<diamond> \<phi>)"
  using IO3_admissible unfolding out3_admissible_def by blast

lemma IO3_CTineq:
  "(\<^bold>\<diamond>\<^sup>3\<^sub>o \<phi>) \<^bold>\<le> (\<^bold>\<diamond>\<^sup>3\<^sub>o (\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>3\<^sub>o \<phi>))"
  using IO3_admissible unfolding out3_admissible_def by blast

lemma IO3_from_norm:
  assumes "\<alpha> \<^bold>\<preceq> \<beta>"
  shows "(\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha>) \<^bold>\<le> \<beta>"
  using IO3_dom assms slanted_from_norm by metis

lemma IO3top: "\<^bold>\<diamond>\<^sup>3\<^sub>o \<^bold>\<top> \<^bold>\<le> \<^bold>\<top>"
  by (simp add: settrue_def)

lemma IO3SI:
  "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<beta> \<^bold>\<le> \<alpha>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<beta> \<^bold>\<le> \<phi>)"
  using IO3_mono unfolding monotone_def by auto

lemma IO3WO:
  "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<phi> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<psi>)"
  by auto

lemma IO3AND:
  "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> (\<phi> \<^bold>\<and> \<psi>))"
  by (simp add: setand_def)

lemma IO3CT:
  "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>3\<^sub>o (\<alpha> \<^bold>\<and> \<phi>) \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<psi>)" 
  by (smt (verit, ccfv_threshold) IO3_CTineq IO3_mono IO_LogicalBase.monotone_def setand_def)


lemma IO3T:
  "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<phi> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<psi>)" 
  by (smt (verit, ccfv_threshold) IO3_CTineq IO3_mono IO_LogicalBase.monotone_def setand_def)

(* -------------------------------------------------------------------------- *)
(* A quick check: OR is not derivable (as expected for out3).       *)
(* -------------------------------------------------------------------------- *)

lemma IO3OR:
  "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<beta> \<^bold>\<le> \<phi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o (\<alpha> \<^bold>\<or> \<beta>) \<^bold>\<le> \<phi>)" 
  nitpick 
  oops

 (* lemma "SF IO" nitpick  *)
 (* lemma "DD IO" nitpick   *)

end