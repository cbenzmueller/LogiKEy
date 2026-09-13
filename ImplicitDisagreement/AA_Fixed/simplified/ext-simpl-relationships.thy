(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains the verification of meta-theoretical connections of extension-based semanticss. 
   Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
*)
theory "ext-simpl-relationships"
  imports "extensions-simpl" "ext-simpl-properties"
begin

(************************************************************************)
(* Inclusion relations as summary: Figure 12 of [BCG2011]
   All verified. The non-inclusion of the inverse directions has been checked
   with Nitpick in every case.  *)
(************************************************************************)

lemma stage_implies_cf_ext: \<open>stageExt AF S \<Longrightarrow> conflictfreeExt AF S\<close>
  by (simp add: maximal_def stageExt_def)

lemma admissible_implies_cf_ext: \<open>admissibleExt AF S \<Longrightarrow> conflictfreeExt AF S\<close>
  by (simp add: admissibleExt_def)

lemma complete_implies_admissible_ext: \<open>completeExt AF S \<Longrightarrow> admissibleExt AF S\<close> 
  by (simp add: completeExt_def)

lemma grounded_implies_complete_ext: \<open>groundedExt AF S \<Longrightarrow> completeExt AF S\<close>
  by (simp add: groundedExt_def minimal_def)

(* Adding a defended argument preserves idealness; maximality therefore
   forces an ideal extension to contain every argument it defends. *)
lemma ideal_implies_complete_ext: "idealExt2 AF S \<Longrightarrow> completeExt AF S"
proof -
  assume ideal: "idealExt2 AF S"
  then have adm: "admissibleExt AF S"
    unfolding idealExt2_def maximal_def idealSet_def by blast
  have defended: "S a" if def: "defends AF S a" for a
  proof -
    have adm_add: "admissibleExt AF (S \<union> \<lbrace>a\<rbrace>)"
      using adm def DungFundLemma1 by blast
    have sub: "(S \<union> \<lbrace>a\<rbrace>) \<subseteq> E" if pref: "preferredExt AF E" for E
    proof -
      have old: "S \<subseteq> E"
        using ideal pref unfolding idealExt2_def maximal_def idealSet_def by blast
      have complete: "completeExt AF E"
        using pref unfolding preferredExt_def maximal_def by blast
      have "defends AF E a"
        using def old unfolding defends_def by blast
      then show ?thesis using complete old unfolding completeExt_def by blast
    qed
    have "idealSet AF (S \<union> \<lbrace>a\<rbrace>)"
      using adm_add sub unfolding idealSet_def by blast
    then show ?thesis using ideal unfolding idealExt2_def maximal_def by auto
  qed
  show ?thesis using adm defended unfolding completeExt_def by blast
qed

lemma preferred_implies_complete_ext: \<open>preferredExt AF S \<Longrightarrow> completeExt AF S\<close>
  by (simp add: maximal_def preferredExt_def)

lemma stable_implies_stage_ext: \<open>stableExt AF S \<Longrightarrow> stageExt AF S\<close>
  by (simp add: greatestMax greatest_def stableExt_def stageExt_def)

lemma semistable_implies_preferred_ext: \<open>semistableExt AF S \<Longrightarrow> preferredExt AF S\<close>  
  unfolding semistableExt_def preferredExt_def maximal_def range_def
  by (smt (verit, ccfv_threshold) admissible_implies_cf_ext complete_implies_admissible_ext conflictfreeExt_def id_apply plusset_def)

lemma stable_implies_semistable_ext: \<open>stableExt AF S \<Longrightarrow> semistableExt AF S\<close>   
  by (smt (verit) range_def admissibleExt_def completeExt_def conflictfreeExt_def defends_def greatestMax greatest_def plusset_def semistableExt_def stableExt_def)

end
