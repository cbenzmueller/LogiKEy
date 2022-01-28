(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains the verification of meta-theoretical connections of labelling-based semanticss. 
   Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
*)
theory "lab-simpl-relationships"
  imports "labellings-simpl"  "lab-simpl-properties"
begin

(************************************************************************)
(* Inclusion relations as summary: Figure 12 of [BCG2011]
   NOT YET All verified. The non-inclusion of the inverse directions has been checked
   with Nitpick in every case.  *)
(************************************************************************)

lemma stage_implies_cf: \<open>stageLab AF Lab \<Longrightarrow> conflictfreeLab AF Lab\<close> 
  by (simp add: stageLab_def minimal_def)

lemma admissible_implies_cf: \<open>admissibleLab AF Lab \<Longrightarrow> conflictfreeLab AF Lab\<close>
  by (simp add: admissibleLab_def conflictfreeLab_def inset_def legallyIn_def legallyOut_def outset_def)

lemma complete_implies_admissible: \<open>completeLab AF Lab \<Longrightarrow> admissibleLab AF Lab\<close> 
  by (simp add: admissibleLab_def completeLab_def)

lemma grounded_implies_complete: \<open>groundedLab AF Lab \<Longrightarrow> completeLab AF Lab\<close>
  by (simp add: groundedLab_def minimal_def)

lemma preferred_implies_complete: \<open>preferredLab AF Lab \<Longrightarrow> completeLab AF Lab\<close>
  by (simp add: preferredLab_def maximal_def)

lemma \<open>idealLab AF Lab \<Longrightarrow> completeLab AF Lab\<close>
  unfolding idealLab_def qidealLab_def unfolding 
  preferredMaxCompleteLabEq 
  unfolding completeLab2_def complete_defEq
  using DungFundLemma1Lab oops (* TODO: still not working...*)
  (* by (smt (z3) DungFundLemma1Lab admissible_EL admissible_LE admissible_def complete2_def complete_defEq defends_def inset_def legallyIn_def legallyOut_def lessOrEquallyCommittedLab_def outset_def plusset_def) *)


lemma \<open>stableLab AF Lab \<Longrightarrow> stageLab AF Lab\<close>
  by (simp add: admissible_implies_cf leastMin least_def stableLab_def stageLab_def complete_implies_admissible undecset_def) 

lemma \<open>semistableLab AF Lab \<Longrightarrow> preferredLab AF Lab \<close> unfolding semistableLab_def preferredLab_def minimal_def maximal_def
  by (smt (verit, ccfv_SIG) Label.exhaust completeLab2_def complete_defEq inset_def legallyOut_def outset_def undecset_def)

lemma \<open>stableLab AF Lab \<Longrightarrow> semistableLab AF Lab\<close> 
  by (simp add: semistableLab_def stableLab_def undecset_def minimal_def)

end
