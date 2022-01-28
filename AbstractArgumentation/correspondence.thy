(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file provides the correspondences between labellings and extensions
   for argumentation frameworks. *)
(* Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
 [Dung 1995] Dung, P.M., On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
            logic programming and n-person games, Artificial Intelligence. (1995)
*)

theory correspondence
  imports extensions labellings "ext-properties"
begin

(**********************************************************)
(**** Correspondences between labellings and extensions ***)
(********** (proved for all but ideal semantics) **********)
(**********************************************************)

(* Define mappings between extensions and labellings. *)
definition Lab2Ext::\<open>'a Labelling \<Rightarrow> 'a Set\<close>
  where \<open>Lab2Ext Lab \<equiv> in(Lab)\<close>
definition Ext2Lab::\<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Labelling\<close> ("Ext2Lab\<^sup>_") (* Warning: works only for conflict-free sets! *)
  where \<open>Ext2Lab\<^sup>\<A> att E \<equiv> \<lambda>a. if (E a) then In else (if ([\<A>|att|E]\<^sup>+ a) then Out else Undec)\<close>

(*conflict-free*)

lemma conflictfree_LE:  "conflictfreeLab\<^sup>\<A> att Lab \<longrightarrow> conflictfreeExt\<^sup>\<A> att (Lab2Ext Lab)"
  by (smt (verit, best) Lab2Ext_def conflictfreeExt_def conflictfreeLab_def legallyOut_def)

lemma conflictfree_LE': "conflictfreeExt\<^sup>\<A> att (Lab2Ext Lab) \<longrightarrow> conflictfreeLab\<^sup>\<A> att Lab"
  nitpick oops (*as expected*)

lemma conflictfree_EL:  "conflictfreeExt\<^sup>\<A> att E \<longrightarrow> conflictfreeLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E)" 
  unfolding conflictfreeExt_def conflictfreeLab_def Ext2Lab_def
  by (smt (verit, best) Label.distinct(1) Label.distinct(3) Label.distinct(5) inset_def legallyOut_def outset_def plusset_rel_def)

lemma conflictfree_EL': "conflictfreeLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E) \<longrightarrow> conflictfreeExt\<^sup>\<A> att E"
  unfolding conflictfreeExt_def conflictfreeLab_def Ext2Lab_def by (smt (z3) inset_def legallyOut_def)

(*admissible*)

lemma admissible_LE:  "admissibleLab\<^sup>\<A> att Lab \<longrightarrow> admissibleExt\<^sup>\<A> att (Lab2Ext Lab)" 
  unfolding admissibleExt_def admissibleLab_def Lab2Ext_def by (smt (verit, ccfv_SIG) Label.distinct(1) conflictfreeExt_def defends_rel_def inset_def legallyIn_def legallyOut_def outset_def)

lemma admissible_LE': "admissibleExt\<^sup>\<A> att (Lab2Ext Lab) \<longrightarrow> admissibleLab\<^sup>\<A> att Lab"
  nitpick oops (*as expected*)

lemma admissible_EL:  "admissibleExt\<^sup>\<A> att E \<longrightarrow> admissibleLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E)"
  unfolding admissibleExt_def admissibleLab_def Ext2Lab_def by (smt (verit, del_insts) Label.distinct(1) Label.distinct(3) Label.distinct(5) conflictfreeExt_def defends_rel_def inset_def legallyIn_def legallyOut_def outset_def plusset_rel_def)

lemma admissible_EL': "admissibleLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E) \<longrightarrow> admissibleExt\<^sup>\<A> att E"
  unfolding admissibleExt_def admissibleLab_def Ext2Lab_def by (smt (verit, del_insts) Label.distinct(1) Label.distinct(5) conflictfreeExt_def defends_rel_def inset_def legallyIn_def outset_def plusset_rel_def)

(*complete*)

lemma complete_LE:  "completeLab\<^sup>\<A> att Lab \<longrightarrow> completeExt\<^sup>\<A> att (Lab2Ext Lab)" 
  unfolding completeExt_def by (smt (verit, ccfv_threshold) Lab2Ext_def admissible_LE completeLab2_def completeLab_def complete_defEq defends_rel_def legallyIn_def legallyOut_def)

lemma complete_LE': "completeExt\<^sup>\<A> att (Lab2Ext Lab) \<longrightarrow> completeLab\<^sup>\<A> att Lab"
  nitpick oops (*as expected*)

lemma complete_EL:  "completeExt\<^sup>\<A> att E \<longrightarrow> completeLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E)"
  unfolding completeExt_def complete_defEq
  by (smt (z3) Ext2Lab_def Label.distinct(1) Label.distinct(3) Label.distinct(5) admissibleExt_def completeLab2_def conflictfreeExt_def defends_rel_def inset_def legallyIn_def legallyOut_def outset_def plusset_rel_def)

lemma complete_EL': "completeLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E) \<longrightarrow> completeExt\<^sup>\<A> att E" 
  unfolding completeExt_def completeLab_def
  by (smt (z3) Ext2Lab_def Label.distinct(1) Label.distinct(3) admissibleLab_def admissible_EL' completeLab2_def completeLab_def complete_defEq conflictfreeExt_def conflictfreeLab_def conflictfree_EL defends_rel_def inset_def legallyIn_def legallyOut_def outset_def plusset_rel_def)

(*preferred*)

lemma preferred_LE:  "preferredLab\<^sup>\<A> att Lab \<longrightarrow> preferredExt\<^sup>\<A> att (Lab2Ext Lab)"
  unfolding preferredExt_def preferredLab_def maximal_rel_def
  by (smt (verit, ccfv_threshold) Ext2Lab_def Lab2Ext_def complete_EL complete_LE id_apply inset_def)

lemma preferred_LE': "preferredExt\<^sup>\<A> att (Lab2Ext Lab) \<longrightarrow> preferredLab\<^sup>\<A> att Lab"
  nitpick oops (*as expected*)

lemma preferred_EL:  "preferredExt\<^sup>\<A> att E \<longrightarrow> preferredLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E)"
  unfolding preferredExt_def preferredLab_def maximal_rel_def
  by (metis Ext2Lab_def Lab2Ext_def complete_EL complete_LE eq_id_iff inset_def)

lemma preferred_EL': "preferredLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E) \<longrightarrow> preferredExt\<^sup>\<A> att E"
  unfolding preferredExt_def preferredLab_def maximal_rel_def
  by (smt (verit) Ext2Lab_def Label.distinct(1) Label.distinct(3) complete_EL complete_EL' id_apply inset_def)

(*grounded*)

lemma grounded_LE:  "groundedLab\<^sup>\<A> att Lab \<longrightarrow> groundedExt\<^sup>\<A> att (Lab2Ext Lab)"
  unfolding groundedExt_def groundedLab_def minimal_rel_def
  by (smt (verit, del_insts) Ext2Lab_def Lab2Ext_def Label.distinct(1) Label.distinct(3) complete_EL complete_LE id_def inset_def)

lemma grounded_LE': "groundedExt\<^sup>\<A> att (Lab2Ext Lab) \<longrightarrow> groundedLab\<^sup>\<A> att Lab"
  nitpick oops (*as expected*)

lemma grounded_EL:  "groundedExt\<^sup>\<A> att E \<longrightarrow> groundedLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E)" 
  unfolding groundedExt_def groundedLab_def minimal_rel_def
  by (metis Ext2Lab_def Lab2Ext_def Label.distinct(1) Label.distinct(3) complete_EL complete_LE id_def inset_def)

lemma grounded_EL': "groundedLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E) \<longrightarrow> groundedExt\<^sup>\<A> att E"
  unfolding groundedExt_def groundedLab_def minimal_rel_def
  by (smt (verit, best) Ext2Lab_def Label.distinct(3) Label.simps(2) complete_EL complete_EL' id_def inset_def)

(*ideal (still missing)*)

lemma ideal_LE:  "idealLab\<^sup>\<A> att Lab \<longrightarrow> idealExt\<^sup>\<A> att (Lab2Ext Lab)"  oops (* TODO: verify *)

lemma ideal_LE': "idealExt\<^sup>\<A> att (Lab2Ext Lab) \<longrightarrow> idealLab\<^sup>\<A> att Lab"
  nitpick oops (*as expected*)

lemma ideal_EL:  "idealExt\<^sup>\<A> att E \<longrightarrow> idealLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E)" oops (* TODO: verify *)

lemma ideal_EL': "idealLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E) \<longrightarrow> idealExt\<^sup>\<A> att E" oops (* TODO: verify *)

(*stable*)

lemma stable_LE:  "stableLab\<^sup>\<A> att Lab \<longrightarrow> stableExt\<^sup>\<A> att (Lab2Ext Lab)"
  unfolding stableExt_def stableLab_def range_def
  by (smt (verit) Lab2Ext_def Label.exhaust admissibleExt_def admissible_LE completeLab2_def completeLab_def complete_defEq inset_def legallyIn_def outset_def plusset_rel_def)

lemma stable_LE': "stableExt\<^sup>\<A> att (Lab2Ext Lab) \<longrightarrow> stableLab\<^sup>\<A> att Lab"
  nitpick oops (*as expected*)

lemma stable_EL:  "stableExt\<^sup>\<A> att E \<longrightarrow> stableLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E)"
  by (smt (verit, ccfv_SIG) range_def Ext2Lab_def Label.distinct(3) Label.distinct(5) completeLab2_def complete_defEq conflictfree_EL conflictfreeLab_def inset_def legallyIn_def legallyOut_def outset_def stableExt_def stableLab_def)

lemma stable_EL': "stableLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E) \<longrightarrow> stableExt\<^sup>\<A> att E"
  unfolding stableExt_def stableLab_def range_def by (metis Ext2Lab_def admissibleExt_def completeAdmissible complete_EL')

(*semi-stable*)

lemma semistable_LE:  "semistableLab\<^sup>\<A> AF Lab \<longrightarrow> semistableExt\<^sup>\<A> AF (Lab2Ext Lab)"
  unfolding semistableExt_def semistableLab_def minimal_rel_def maximal_rel_def
  by (smt (verit, best) Ext2Lab_def Lab2Ext_def Label.exhaust completeLab2_def complete_EL complete_LE complete_defEq inset_def legallyOut_def outset_def plusset_rel_def range_def undecset_def)

lemma semistable_LE': "semistableExt\<^sup>\<A> AF (Lab2Ext Lab) \<longrightarrow> semistableLab\<^sup>\<A> AF Lab"
  nitpick oops (*as expected*)

lemma semistable_EL:  "semistableExt\<^sup>\<A> AF E \<longrightarrow> semistableLab\<^sup>\<A> AF (Ext2Lab\<^sup>\<A> AF E)"
  unfolding semistableExt_def semistableLab_def minimal_rel_def maximal_rel_def 
  by (smt (verit, best) Ext2Lab_def Lab2Ext_def Label.distinct(3) Label.exhaust Label.simps(6) admissibleLab_def completeLab_def complete_EL complete_LE inset_def legallyOut_def outset_def plusset_rel_def range_def undecset_def)
 
lemma semistable_EL': "semistableLab\<^sup>\<A> AF (Ext2Lab\<^sup>\<A> AF E) \<longrightarrow> semistableExt\<^sup>\<A> AF E"
  unfolding semistableExt_def semistableLab_def  minimal_rel_def maximal_rel_def
  by (smt (verit, ccfv_threshold) Ext2Lab_def Label.distinct(3) Label.simps(6) complete_EL complete_EL' range_def undecset_def)


(*stage*)

lemma stage_LE:  "stageLab\<^sup>\<A> att Lab \<longrightarrow> stageExt\<^sup>\<A> att (Lab2Ext Lab)" 
  unfolding stageExt_def stageLab_def minimal_rel_def maximal_rel_def range_def
  by (smt (verit) Ext2Lab_def Lab2Ext_def Label.distinct(5) Label.exhaust conflictfree_EL conflictfree_LE conflictfreeLab_def inset_def legallyOut_def outset_def plusset_rel_def undecset_def)

lemma stage_LE': "stageExt\<^sup>\<A> att (Lab2Ext Lab) \<longrightarrow> stageLab\<^sup>\<A> att Lab"
  nitpick oops (*as expected*)

lemma stage_EL:  "stageExt\<^sup>\<A> AF E \<longrightarrow> stageLab\<^sup>\<A> AF (Ext2Lab\<^sup>\<A> AF E)"
  unfolding stageExt_def stageLab_def minimal_rel_def maximal_rel_def
  by (smt (verit, del_insts) Ext2Lab_def Lab2Ext_def Label.exhaust conflictfree_EL conflictfree_LE conflictfreeLab_def inset_def legallyOut_def outset_def plusset_rel_def range_def undecset_def)

lemma stage_EL': "stageLab\<^sup>\<A> att (Ext2Lab\<^sup>\<A> att E) \<longrightarrow> stageExt\<^sup>\<A> att E"
  unfolding stageExt_def stageLab_def minimal_rel_def maximal_rel_def range_def
  by (smt (verit, ccfv_threshold) Ext2Lab_def Label.distinct(3) Label.distinct(6) conflictfree_EL conflictfree_EL' undecset_def)

end
