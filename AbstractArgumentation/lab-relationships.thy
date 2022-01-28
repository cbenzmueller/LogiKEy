(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains the verification of meta-theoretical connections of labelling-based semanticss. 
   Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
*)
theory "lab-relationships"
  imports "labellings"  "lab-properties"
begin


(************************************************************************)
(* Inclusion relations as summary: Figure 12 of [BCG2011]
   All but one verified. The non-inclusion of the inverse directions has been checked
   with Nitpick in every case.  *)
(************************************************************************)

lemma stage_implies_cf: \<open>stageLab\<^sup>\<A> AF Lab \<Longrightarrow> conflictfreeLab\<^sup>\<A> AF Lab\<close> 
  by (simp add: minimal_rel_def stageLab_def)
 
lemma admissible_implies_cf: \<open>admissibleLab\<^sup>\<A> AF Lab \<Longrightarrow> conflictfreeLab\<^sup>\<A> AF Lab\<close>
  by (simp add: admissibleLab_def conflictfreeLab_def inset_def legallyIn_def legallyOut_def outset_def)

lemma complete_implies_admissible: \<open>completeLab\<^sup>\<A> AF Lab \<Longrightarrow> admissibleLab\<^sup>\<A> AF Lab\<close> 
  by (simp add: admissibleLab_def completeLab_def)

lemma grounded_implies_complete: \<open>groundedLab\<^sup>\<A> AF Lab \<Longrightarrow> completeLab\<^sup>\<A> AF Lab\<close>
  by (simp add: groundedLab_def minimal_rel_def)

lemma preferred_implies_complete: \<open>preferredLab\<^sup>\<A> AF Lab \<Longrightarrow> completeLab\<^sup>\<A> AF Lab\<close> 
  by (simp add: maximal_rel_def preferredLab_def)

lemma \<open>idealLab\<^sup>\<A> AF Lab \<Longrightarrow> completeLab\<^sup>\<A> AF Lab\<close>
  oops (* TODO *)
  
lemma \<open>stableLab\<^sup>\<A> AF Lab \<Longrightarrow> stageLab\<^sup>\<A> AF Lab\<close>
  by (simp add: admissible_implies_cf leastMin_rel least_rel_def stableLab_def stageLab_def complete_implies_admissible undecset_def) 

lemma \<open>semistableLab\<^sup>\<A> AF Lab \<Longrightarrow> preferredLab\<^sup>\<A> AF Lab \<close> unfolding semistableLab_def preferredLab_def minimal_rel_def maximal_rel_def
  by (smt (verit, ccfv_SIG) Label.exhaust completeLab2_def complete_defEq inset_def legallyOut_def outset_def undecset_def)

lemma \<open>stableLab\<^sup>\<A> AF Lab \<Longrightarrow> semistableLab\<^sup>\<A> AF Lab\<close> 
  by (simp add: semistableLab_def stableLab_def undecset_def minimal_rel_def)

end
