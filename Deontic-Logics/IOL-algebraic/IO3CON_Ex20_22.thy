theory IO3CON_Ex20_22
  imports IO3CON
begin

(* ******************************************************************************
 * Examples from book: 
 * Parent & van der Torre, Introduction to Deontic Logic and Normative Systems 
 * Chapter 4, Examples 20-22 (Chisholm)
 *
 ******************************************************************************)

consts h :: "\<tau>"   (* helping *)
consts t :: "\<tau>"   (* telling *)

(* -------------------------------------------------------------------------- *)
(* A                                                        *)
(* -------------------------------------------------------------------------- *)

definition A_not_h :: "\<tau> \<Rightarrow> bool" where
  "A_not_h \<equiv> (\<lambda>\<phi>. \<phi> = \<^bold>\<not>h)"

definition A_h :: "\<tau> \<Rightarrow> bool" where
  "A_h \<equiv> (\<lambda>\<phi>. \<phi> = h)"


(* -------------------------------------------------------------------------- *)
(* NS                                                                    *)
(* -------------------------------------------------------------------------- *)

definition N_ch :: normsys where
  "N_ch a b \<equiv> (a = \<^bold>\<top> \<and> b = h)
               \<or> (a = h \<and> b = t)
               \<or> (a = \<^bold>\<not>h \<and> b = \<^bold>\<not>t)"

definition N_ch_repair :: normsys where
  "N_ch_repair a b \<equiv> (a = h \<and> b = t)
                      \<or> (a = \<^bold>\<not>h \<and> b = \<^bold>\<not>t)"

lemma N_ch_r1[simp]: "N_ch \<^bold>\<top> h"
  by (simp add: N_ch_def)

lemma N_ch_r2[simp]: "N_ch h t"
  by (simp add: N_ch_def)

lemma N_ch_r3[simp]: "N_ch (\<^bold>\<not>h) (\<^bold>\<not>t)"
  by (simp add: N_ch_def)

lemma N_ch_repair_r2[simp]: "N_ch_repair h t"
  by (simp add: N_ch_repair_def)

lemma N_ch_repair_r3[simp]: "N_ch_repair (\<^bold>\<not>h) (\<^bold>\<not>t)"
  by (simp add: N_ch_repair_def)

lemma N_ch_repair_subset_N_ch:
  "N_ch_repair \<^bold>\<sqsubseteq> N_ch"
  by (auto simp: N_ch_repair_def N_ch_def)

lemma subset_N_ch_without_primary_subset_repair:
  assumes "M \<^bold>\<sqsubseteq> N_ch"
      and "\<not> M \<^bold>\<top> h"
  shows "M \<^bold>\<sqsubseteq> N_ch_repair"
  using assms by (auto simp: N_ch_def N_ch_repair_def)

lemma ch_A_not_h_infimum:
  "\<^bold>\<And>A_not_h = \<^bold>\<not>h"
  unfolding A_not_h_def by (rule infimum_singleton)

lemma ch_A_h_infimum:
  "\<^bold>\<And>A_h = h"
  unfolding A_h_def by (rule infimum_singleton)

lemma chisholm_primary_conflicts_with_constraint:
  assumes "N \<^bold>\<top> h"
  shows "\<not> out_consistent N A_not_h A_not_h" 
proof -
  have h_from_top: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N \<^bold>\<top>) \<^bold>\<le> h"  
    using IO3N_from_norm assms by auto
  have h_from_not_h: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N (\<^bold>\<not>h)) \<^bold>\<le> h" 
    by (metis IO3N_mono IO_LogicalBase.monotone_def h_from_top settrue_def)
  have out_h: "out3 N A_not_h h" 
    by (simp add: ch_A_not_h_infimum h_from_not_h out3_def)
  have clash: "(h \<^bold>\<and> \<^bold>\<And>A_not_h) = \<^bold>\<bottom>"
    unfolding ch_A_not_h_infimum by (simp add: setand_def setnot_def setfalse_def)
  show ?thesis
  using clash not_out_consistent_from_output_constraint_conflict out_h by auto
qed

lemma chisholm_example20_bottom:
  "out3 N_ch A_not_h \<^bold>\<bottom>" 
proof -
  have h_from_top: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N_ch \<^bold>\<top>) \<^bold>\<le> h" 
    using IO3N_from_norm N_ch_r1 by blast
  have h_from_not_h: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N_ch (\<^bold>\<not>h)) \<^bold>\<le> h"
    by (metis IO3N_mono IO_LogicalBase.monotone_def h_from_top settrue_def)
  have t_from_h: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N_ch h) \<^bold>\<le> t" 
    using IO3N_from_norm N_ch_r2 by blast
  have t_from_not_h_and_h: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N_ch ((\<^bold>\<not>h) \<^bold>\<and> h)) \<^bold>\<le> t"
    by (meson IO3N_mono[of N_ch] IO_LogicalBase.monotone_def[of "\<^bold>\<diamond>\<^sup>3\<^sub>c N_ch"] setand_def[of "\<^bold>\<not>h" h] t_from_h)
  have t_from_not_h: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N_ch (\<^bold>\<not>h)) \<^bold>\<le> t"
  using IO3N_CT h_from_not_h t_from_not_h_and_h by blast
  have not_t_from_not_h: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N_ch (\<^bold>\<not>h)) \<^bold>\<le> (\<^bold>\<not>t)"
    using IO3N_from_norm by (metis N_ch_r3)
  have both: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N_ch (\<^bold>\<not>h)) \<^bold>\<le> (t \<^bold>\<and> \<^bold>\<not>t)"
  by (simp add: not_t_from_not_h setand_def t_from_not_h)
  have bot: "(\<^bold>\<diamond>\<^sup>3\<^sub>c N_ch (\<^bold>\<not>h)) \<^bold>\<le> \<^bold>\<bottom>"
    using not_t_from_not_h setnot_def t_from_not_h by auto
  show ?thesis
    using out3_singletonI[OF bot] unfolding A_not_h_def by simp
qed

lemma chisholm_example20_L:
  "out3 N_ch A_not_h \<psi>"
  using out3_bottom_all[OF chisholm_example20_bottom] .

lemma chisholm_example20_inconsistent:
  "\<not> out_consistent N_ch A_not_h A_not_h"
  using not_out_consistent_if_bottom_output[OF chisholm_example20_bottom] .

context
  assumes chisholm22_cons: "out_consistent N_ch_repair A_not_h A_not_h"
      and chisholm22_cons_full: "out_consistent N_ch A_h A_h"
begin

lemma chisholm22_repair_maxfamily:
  "maxfamily N_ch A_not_h A_not_h N_ch_repair" 
  by (smt (verit) N_ch_repair_subset_N_ch ch_A_h_infimum 
      chisholm22_cons chisholm_primary_conflicts_with_constraint
      maxfamily_def subset_N_ch_without_primary_subset_repair)

lemma chisholm22_unique_maxfamily:
  "maxfamily N_ch A_not_h A_not_h N0 \<longleftrightarrow> N0 = N_ch_repair"
proof
  assume mf: "maxfamily N_ch A_not_h A_not_h N0"
  have n0sub: "N0 \<^bold>\<sqsubseteq> N_ch"
    using mf unfolding maxfamily_def by blast
  have n0cons: "out_consistent N0 A_not_h A_not_h"
    using mf unfolding maxfamily_def by blast
  have no_primary: "\<not> N0 \<^bold>\<top> h"
  proof
    assume "N0 \<^bold>\<top> h"
    hence "\<not> out_consistent N0 A_not_h A_not_h"
      using chisholm_primary_conflicts_with_constraint by blast
    with n0cons show False by contradiction
  qed
  have n0subrepair: "N0 \<^bold>\<sqsubseteq> N_ch_repair"
    using subset_N_ch_without_primary_subset_repair[OF n0sub no_primary] .
  have repairsub: "N_ch_repair \<^bold>\<sqsubseteq> N0"
    using mf chisholm22_cons N_ch_repair_subset_N_ch n0subrepair unfolding maxfamily_def by blast
  show "N0 = N_ch_repair"
    using n0subrepair repairsub by blast
next
  assume "N0 = N_ch_repair"
  thus "maxfamily N_ch A_not_h A_not_h N0"
    using chisholm22_repair_maxfamily by simp
qed

lemma chisholm22_skep_not_t:
  "skep_out_ctd N_ch A_not_h (\<^bold>\<not>t)" 
  by (metis IO3N_from_norm N_ch_repair_r3 ch_A_not_h_infimum chisholm22_unique_maxfamily out3_def outfamily_iff skepoutfamily_def)

lemma chisholm22_cred_not_t:
  "cred_out_ctd N_ch A_not_h (\<^bold>\<not>t)" 
  using chisholm22_repair_maxfamily chisholm22_skep_not_t credoutfamily_def outfamily_iff skepoutfamily_def by auto

lemma chisholm22_compliant_unique_maxfamily:
  "maxfamily N_ch A_h A_h N0 \<longleftrightarrow> N0 = N_ch" 
proof
  assume mf: "maxfamily N_ch A_h A_h N0"
  have n0sub: "N0 \<^bold>\<sqsubseteq> N_ch"
    using mf unfolding maxfamily_def by blast
  have fullsub: "N_ch \<^bold>\<sqsubseteq> N0"
    using mf chisholm22_cons_full n0sub unfolding maxfamily_def by blast
  show "N0 = N_ch"
    using n0sub fullsub by blast
next
  assume "N0 = N_ch"
  moreover have "maxfamily N_ch A_h A_h N_ch"
    using chisholm22_cons_full unfolding maxfamily_def by auto
  ultimately show "maxfamily N_ch A_h A_h N0"
    by simp
qed

lemma chisholm22_compliant_skep_h:
  "skep_out_ctd N_ch A_h h" 
  by (metis (mono_tags, lifting) IO3N_admissible IO3N_from_norm IO_LogicalBase.monotone_def N_ch_r1 ch_A_h_infimum
      chisholm22_compliant_unique_maxfamily out3_admissibleN_def out3_def outfamily_iff settrue_def skepoutfamily_def)

lemma chisholm22_compliant_skep_t:
  "skep_out_ctd N_ch A_h t" 
  by (metis IO3N_from_norm N_ch_r2 ch_A_h_infimum chisholm22_compliant_unique_maxfamily out3_def outfamily_iff skepoutfamily_def)

end

end
