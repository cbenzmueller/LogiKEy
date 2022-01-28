(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains the verification of meta-theoretical connections of extension-based semantics. 
   Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
*)
theory "ext-relationships"
  imports "extensions" "ext-properties"
begin

(************************************************************************)
(* Inclusion relations as summary: Figure 12 of [BCG2011]
   All but one verified. The non-inclusion of the inverse directions has been checked
   with Nitpick in every case.  *)
(************************************************************************)

lemma stage_implies_cf_ext: \<open>stageExt\<^sup>\<A> AF S \<Longrightarrow> conflictfreeExt\<^sup>\<A> AF S\<close>
  by (simp add: maximal_rel_def stageExt_def)

lemma admissible_implies_cf_ext: \<open>admissibleExt\<^sup>\<A> AF S \<Longrightarrow> conflictfreeExt\<^sup>\<A> AF S\<close>
  by (simp add: admissibleExt_def)

lemma complete_implies_admissible_ext: \<open>completeExt\<^sup>\<A> AF S \<Longrightarrow> admissibleExt\<^sup>\<A> AF S\<close> 
  by (simp add: completeExt_def)

lemma grounded_implies_complete_ext: \<open>groundedExt\<^sup>\<A> AF S \<Longrightarrow> completeExt\<^sup>\<A> AF S\<close>
  by (simp add: groundedExt_def minimal_rel_def)


lemma ideal_implies_complete_ext: \<open>idealExt2\<^sup>\<A> AF S \<Longrightarrow> completeExt\<^sup>\<A> AF S\<close> 
  oops (*TODO*)

lemma preferred_implies_complete_ext: \<open>preferredExt\<^sup>\<A> AF S \<Longrightarrow> completeExt\<^sup>\<A> AF S\<close>
  by (simp add: maximal_rel_def preferredExt_def)

lemma stable_implies_stage_ext: \<open>stableExt\<^sup>\<A> AF S \<Longrightarrow> stageExt\<^sup>\<A> AF S\<close>
  by (simp add: greatestMax_rel greatest_rel_def stableExt_def stageExt_def)

lemma semistable_implies_preferred_ext: \<open>semistableExt\<^sup>\<A> AF S \<Longrightarrow> preferredExt\<^sup>\<A> AF S\<close>  
  unfolding semistableExt_def preferredExt_def maximal_rel_def range_def
  by (smt (z3) admissible_implies_cf_ext complete_implies_admissible_ext conflictfreeExt_def id_apply plusset_rel_def)
  
                                                                                                                                
lemma stable_implies_semistable_ext: \<open>stableExt\<^sup>\<A> AF S \<Longrightarrow> semistableExt\<^sup>\<A> AF S\<close>   
  by (smt (verit, ccfv_threshold) admissibleExt_def completeExt_def conflictfreeExt_def defends_rel_def greatestMax_rel greatest_rel_def plusset_rel_def range_def semistableExt_def stableExt_def)

end
