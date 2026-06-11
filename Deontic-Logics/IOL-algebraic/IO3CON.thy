theory IO3CON
  imports IO3 IO_CON
begin

(******************************************************************************)
(* Constrained Input/Output Logic (output 3)                                  *)
(*                                                                            *)
(* Design choices:                                                            *)
(*   1. We keep the unconstrained operators from IO3 intact.                  *)
(*      The constrained layer therefore uses distinct names/slanted aliases:  *)
(*        slantedN  /  \<^bold>\<diamond>\<^sub>c                                                     *)
(*        IO3N      /  \<^bold>\<diamond>\<^sup>3\<^sub>c                                                    *)
(*   2. Gross output on an input family A is represented directly by          *)
(*        out3 N A \<psi>  \<equiv>  IO3N N (\<And>A) \<le> \<psi>.                                   *)
(*   3. maxfamily/outfamily follow the usual constrained-I/O presentation.    *)
(******************************************************************************)

definition out3_admissibleN :: "normsys \<Rightarrow> (\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where
  "out3_admissibleN N op \<equiv>
      monotone op
    \<and> (\<forall>\<phi>. op \<phi> \<^bold>\<le> op (\<phi> \<^bold>\<and> op \<phi>))
    \<and> (\<forall>\<phi>. op \<phi> \<^bold>\<le> (\<^bold>\<diamond>\<^sub>c N \<phi>))"

definition largest_out3N :: "normsys \<Rightarrow> (\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where
  "largest_out3N N op \<equiv>
      out3_admissibleN N op
    \<and> (\<forall>op1. out3_admissibleN N op1 \<longrightarrow> (\<forall>\<phi>. op1 \<phi> \<^bold>\<le> op \<phi>))"

consts IO3N :: "normsys \<Rightarrow> \<tau> \<Rightarrow> \<tau>" ("\<^bold>\<diamond>\<^sup>3\<^sub>c")

axiomatization where
  ax_IO3N: "\<forall>N. largest_out3N N (\<^bold>\<diamond>\<^sup>3\<^sub>c N)"

lemma IO3N_admissible: "out3_admissibleN N (\<^bold>\<diamond>\<^sup>3\<^sub>c N)"
  using ax_IO3N unfolding largest_out3N_def by blast

lemma IO3N_mono: "monotone (\<^bold>\<diamond>\<^sup>3\<^sub>c N)"
  using IO3N_admissible unfolding out3_admissibleN_def by blast

lemma IO3N_dom: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<phi>) \<^bold>\<le> (\<^bold>\<diamond>\<^sub>c N \<phi>)"
  using IO3N_admissible unfolding out3_admissibleN_def by blast

lemma IO3N_CTineq:
  "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<phi>) \<^bold>\<le> (\<^bold>\<diamond>\<^sup>3\<^sub>c N (\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>3\<^sub>c N \<phi>))"
  using IO3N_admissible unfolding out3_admissibleN_def by blast

lemma IO3N_from_norm:
  assumes "N \<alpha> \<beta>"
  shows "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> \<beta>" 
  using IO3N_dom assms slantedN_from_norm by blast

(* Gross output on a family of factual inputs A. *)
definition out3 :: "normsys \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> \<tau> \<Rightarrow> bool"
  where "out3 N A \<psi> \<equiv> (\<^bold>\<diamond>\<^sup>3\<^sub>c N (\<^bold>\<And>A)) \<^bold>\<le> \<psi>"

(* Consistency of out3(N,A) with the constraint set C. *)
definition out_consistent :: "normsys \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> bool"
  where "out_consistent N A C \<equiv> \<not> (((\<^bold>\<diamond>\<^sup>3\<^sub>c N (\<^bold>\<And>A)) \<^bold>\<and> (\<^bold>\<And>C)) = \<^bold>\<bottom>)"

definition maxfamily :: "normsys \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> normsys \<Rightarrow> bool"
  where
  "maxfamily N A C N0 \<equiv>
       N0 \<^bold>\<sqsubseteq> N
     \<and> out_consistent N0 A C
     \<and> (\<forall>N1. N0 \<^bold>\<sqsubseteq> N1 \<and> N1 \<^bold>\<sqsubseteq> N \<and> out_consistent N1 A C \<longrightarrow> N1 \<^bold>\<sqsubseteq> N0)"

definition outfamily :: "normsys \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> bool"
  where "outfamily N A C B \<equiv> \<exists>N0. maxfamily N A C N0 \<and> B = out3 N0 A"

definition skepoutfamily :: "normsys \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> \<tau> \<Rightarrow> bool"
  where "skepoutfamily N A C \<psi> \<equiv> \<forall>B. outfamily N A C B \<longrightarrow> B \<psi>"

definition credoutfamily :: "normsys \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> \<tau> \<Rightarrow> bool"
  where "credoutfamily N A C \<psi> \<equiv> \<exists>B. outfamily N A C B \<and> B \<psi>"

abbreviation (input) skep_out_ctd :: "normsys \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> \<tau> \<Rightarrow> bool"
  where "skep_out_ctd N A \<equiv> skepoutfamily N A A"

abbreviation (input) cred_out_ctd :: "normsys \<Rightarrow> (\<tau> \<Rightarrow> bool) \<Rightarrow> \<tau> \<Rightarrow> bool"
  where "cred_out_ctd N A \<equiv> credoutfamily N A A"

lemma maxfamily_subset:
  assumes "maxfamily N A C N0"
  shows "N0 \<^bold>\<sqsubseteq> N"
  using assms unfolding maxfamily_def by blast

lemma maxfamily_consistent:
  assumes "maxfamily N A C N0"
  shows "out_consistent N0 A C"
  using assms unfolding maxfamily_def by blast

lemma outfamily_iff:
  "outfamily N A C B \<longleftrightarrow> (\<exists>N0. maxfamily N A C N0 \<and> B = out3 N0 A)"
  unfolding outfamily_def by blast

(* tests, check from here *)

lemma infimum_singleton:
  "\<^bold>\<And>(\<lambda>x. x = p) = p"
  by (rule ext, simp add: infimum_def)

lemma infimum_contains_bottom:
  assumes "S \<^bold>\<bottom>"
  shows "\<^bold>\<And>S = \<^bold>\<bottom>"
  using assms 
  using infimum_member setfalse_def by fastforce

lemma infimum_member_lower:
  assumes "S X"
  shows "\<^bold>\<And>S \<^bold>\<le> X"
  using assms unfolding infimum_def by auto

(* -------------------------------------------------------------------------- *)
(* Useful derived rules for the parameterized output-3 operator                *)
(* -------------------------------------------------------------------------- *)

lemma IO3N_SI:
  assumes "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> \<phi>"
      and "\<beta> \<^bold>\<le> \<alpha>"
  shows "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<beta>) \<^bold>\<le> \<phi>"
  using IO3N_mono assms unfolding monotone_def by auto

lemma IO3N_WO:
  assumes "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> \<phi>"
      and "\<phi> \<^bold>\<le> \<psi>"
  shows "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> \<psi>"
  using assms by auto

lemma IO3N_AND:
  assumes "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> \<phi>"
      and "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> \<psi>"
  shows "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> (\<phi> \<^bold>\<and> \<psi>)"
  using assms by (simp add: setand_def)

lemma IO3N_CT:
  assumes h1: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> \<phi>"
      and h2: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N (\<alpha> \<^bold>\<and> \<phi>)) \<^bold>\<le> \<psi>"
    shows "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> \<psi>"  
proof -
  have fix1: "\<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>c N (\<alpha> \<^bold>\<and> \<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>)"
    using IO3N_CTineq .
  have le1: "(\<alpha> \<^bold>\<and> \<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> (\<alpha> \<^bold>\<and> \<phi>)"
    using h1 by (simp add: setand_def)
  have mono: "\<^bold>\<diamond>\<^sup>3\<^sub>c N (\<alpha> \<^bold>\<and> \<^bold>\<diamond>\<^sup>3\<^sub>c N \<alpha>) \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>c N (\<alpha> \<^bold>\<and> \<phi>)"
    using IO3N_mono le1 unfolding monotone_def by auto
  show ?thesis
    using fix1 mono h2 by auto
qed

(* -------------------------------------------------------------------------- *)
(* Gross output as a set of formulas                                           *)
(* -------------------------------------------------------------------------- *)

lemma out3_singletonI:
  assumes "(\<^bold>\<diamond>\<^sup>3\<^sub>c N p) \<^bold>\<le> \<psi>"
  shows "out3 N (\<lambda>x. x = p) \<psi>" 
  by (simp add: assms out3_def)

lemma out3_WO:
  assumes "out3 N A \<phi>"
      and "\<phi> \<^bold>\<le> \<psi>"
  shows "out3 N A \<psi>"
  using assms unfolding out3_def by blast

lemma out3_bottom_all:
  assumes "out3 N A \<^bold>\<bottom>"
  shows "out3 N A \<psi>"
  using out3_WO[OF assms] 
  by (simp add: setfalse_def)

lemma not_out_consistent_if_bottom_output:
  assumes "out3 N A \<^bold>\<bottom>"
  shows "\<not> out_consistent N A C" 
  unfolding infimum_def out3_def out_consistent_def setand_def setfalse_def
  using  assms
  by (simp add: infimum_def out3_def setfalse_def)

lemma not_out_consistent_from_output_constraint_conflict:
  assumes outphi: "out3 N A \<phi>"
      and clash: "(\<phi> \<^bold>\<and> \<^bold>\<And>C) = \<^bold>\<bottom>"
    shows "\<not> out_consistent N A C"
  unfolding out3_def out_consistent_def outphi setand_def setfalse_def
  using clash 
  by (metis out3_def outphi setand_def setfalse_def)

end
