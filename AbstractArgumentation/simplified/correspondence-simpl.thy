theory "correspondence-simpl"
  imports "extensions-simpl" "labellings-simpl"  "ext-simpl-properties"
begin

(**********************************************************)
(**** Correspondences between labellings and extensions ***)
(********** (proved for all but ideal semantics) **********)
(**********************************************************)

(* Define mappings between extensions and labellings. *)
definition Lab2Ext::\<open>'a Labelling \<Rightarrow> 'a Set\<close>
  where \<open>Lab2Ext Lab \<equiv> in(Lab)\<close>
definition Ext2Lab::\<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Labelling\<close> (* Warning: works only for conflict-free sets! *)
  where \<open>Ext2Lab AF E \<equiv> \<lambda>a. if (E a) then In else (if ([AF|E]\<^sup>+ a) then Out else Undec)\<close>

(*conflict-free*)

lemma conflictfree_LE:  "conflictfreeLab AF Lab \<longrightarrow> conflictfreeExt AF (Lab2Ext Lab)" 
  by (metis (mono_tags, lifting) Lab2Ext_def conflictfreeExt_def conflictfreeLab_def legallyOut_def)

lemma conflictfree_LE': "conflictfreeExt AF (Lab2Ext Lab) \<longrightarrow> conflictfree AF Lab"
  nitpick oops (*as expected*)

lemma conflictfree_EL:  "conflictfreeExt AF E \<longrightarrow> conflictfreeLab AF (Ext2Lab AF E)" 
  unfolding conflictfreeExt_def conflictfreeLab_def Ext2Lab_def
  by (smt (verit, best) Label.distinct(1) Label.distinct(3) Label.distinct(5) inset_def legallyOut_def outset_def plusset_def)

lemma conflictfree_EL': "conflictfreeLab AF (Ext2Lab AF E) \<longrightarrow> conflictfreeExt AF E"
  unfolding Ext2Lab_def conflictfreeExt_def conflictfreeLab_def by (simp add: inset_def legallyOut_def)

(*admissible*)

lemma admissible_LE:  "admissibleLab AF Lab \<longrightarrow> admissibleExt AF (Lab2Ext Lab)" 
  unfolding admissibleExt_def admissibleLab_def Lab2Ext_def
  by (metis (mono_tags, hide_lams) Label.distinct(1) defends_def conflictfreeExt_def inset_def legallyIn_def legallyOut_def outset_def)

lemma admissible_LE': "admissibleExt AF (Lab2Ext Lab) \<longrightarrow> admissible AF Lab"
  nitpick oops (*as expected*)

lemma admissible_EL:  "admissibleExt AF E \<longrightarrow> admissibleLab AF (Ext2Lab AF E)"
  unfolding admissibleExt_def admissibleLab_def Ext2Lab_def
  by (smt (verit, del_insts) Label.distinct(1) Label.distinct(3) Label.distinct(5) defends_def conflictfreeExt_def inset_def legallyIn_def legallyOut_def outset_def plusset_def)

lemma admissible_EL': "admissibleLab AF (Ext2Lab AF E) \<longrightarrow> admissibleExt AF E"
  unfolding admissibleExt_def admissibleLab_def Ext2Lab_def
  by (smt (verit, best) Label.distinct(1) Label.distinct(5) conflictfreeExt_def defends_defEq inset_def legallyIn_def minusset_def outset_def)

(*complete*)

lemma complete_LE:  "completeLab AF Lab \<longrightarrow> completeExt AF (Lab2Ext Lab)" 
  unfolding completeExt_def  
  by (metis Lab2Ext_def admissible_LE completeLab2_def completeLab_def complete_defEq defends_def legallyIn_def legallyOut_def)

lemma complete_LE': "completeExt AF (Lab2Ext Lab) \<longrightarrow> complete AF Lab"
  nitpick oops (*as expected*)

lemma complete_EL:  "completeExt AF E \<longrightarrow> completeLab AF (Ext2Lab AF E)"
  unfolding completeExt_def complete_defEq Ext2Lab_def
  by (smt (z3) Label.distinct(1) Label.distinct(3) Label.distinct(5) admissibleExt_def completeLab2_def conflictfreeExt_def defends_def inset_def legallyIn_def legallyOut_def outset_def plusset_def)

lemma complete_EL': "completeLab AF (Ext2Lab AF E) \<longrightarrow> completeExt AF E" 
  unfolding completeExt_def completeLab_def Ext2Lab_def
  by (smt (verit, del_insts) Label.distinct(1) Label.distinct(3) MONO_def \<F>_mono admissibleExt_def complete_LE Lab2Ext_def completeLab_def completeExt_def conflictfreeExt_def inset_def) 

(*preferred*)

lemma preferred_LE:  "preferredLab AF Lab \<longrightarrow> preferredExt AF (Lab2Ext Lab)"
  unfolding preferredExt_def preferredLab_def maximal_def
  by (smt (verit, ccfv_SIG) Label.distinct(1) Label.distinct(3) Ext2Lab_def Lab2Ext_def complete_EL complete_LE id_apply inset_def)

lemma preferred_LE': "preferredExt AF (Lab2Ext Lab) \<longrightarrow> preferred AF Lab"
  nitpick oops (*as expected*)

lemma preferred_EL:  "preferredExt AF E \<longrightarrow> preferredLab AF (Ext2Lab AF E)"
  unfolding preferredExt_def preferredLab_def maximal_def
  by (metis Ext2Lab_def Lab2Ext_def complete_EL complete_LE id_def inset_def)

lemma preferred_EL': "preferredLab AF (Ext2Lab AF E) \<longrightarrow> preferredExt AF E"
  unfolding preferredExt_def preferredLab_def maximal_def
  by (smt (verit) Ext2Lab_def Lab2Ext_def Label.distinct(1) Label.distinct(3) complete_EL complete_EL' id_def inset_def)

(*grounded*)

lemma grounded_LE:  "groundedLab AF Lab \<longrightarrow> groundedExt AF (Lab2Ext Lab)"
  unfolding groundedExt_def groundedLab_def minimal_def
  by (smt (verit) Ext2Lab_def Lab2Ext_def Label.distinct(2) Label.distinct(4) complete_EL complete_LE id_def inset_def)

lemma grounded_LE': "groundedExt AF (Lab2Ext Lab) \<longrightarrow> grounded AF Lab"
  nitpick oops (*as expected*)

lemma grounded_EL:  "groundedExt AF E \<longrightarrow> groundedLab AF (Ext2Lab AF E)"
  unfolding groundedExt_def groundedLab_def minimal_def
  by (metis Ext2Lab_def Lab2Ext_def Label.distinct(1) Label.distinct(3) complete_EL complete_LE id_def inset_def)

lemma grounded_EL': "groundedLab AF (Ext2Lab AF E) \<longrightarrow> groundedExt AF E"
  unfolding groundedExt_def groundedLab_def minimal_def
  by (smt (verit, del_insts) Ext2Lab_def Label.distinct(2) Label.distinct(3) complete_EL complete_EL' id_apply inset_def)

(*ideal (still missing)*)

lemma ideal_LE:  "idealLab AF Lab \<Longrightarrow> idealExt AF (Lab2Ext Lab)" oops (* TODO: verify *)

lemma ideal_LE': "idealExt AF (Lab2Ext Lab) \<longrightarrow> idealLab AF Lab"
  nitpick oops (*as expected*)

lemma ideal_EL:  "idealExt AF E \<longrightarrow> idealLab AF (Ext2Lab AF E)" oops (* TODO: verify *)

lemma ideal_EL': "idealLab AF (Ext2Lab AF E) \<longrightarrow> idealExt AF E" oops (* TODO: verify *)

(*stable*)

lemma stable_LE:  "stableLab AF Lab \<longrightarrow> stableExt AF (Lab2Ext Lab)"
  unfolding stableExt_def stableLab_def range_def
  by (metis (full_types) Lab2Ext_def Label.exhaust admissibleExt_def completeLab2_def completeExt_def complete_LE complete_defEq inset_def legallyIn_def outset_def plusset_def)

lemma stable_LE': "stableExt AF (Lab2Ext Lab) \<longrightarrow> stable AF Lab"
  nitpick oops (*as expected*)

lemma stable_EL:  "stableExt AF E \<longrightarrow> stableLab AF (Ext2Lab AF E)"
  by (smt (verit) range_def Ext2Lab_def Label.distinct(4) Label.distinct(6) admissibleExt_def admissible_EL completeLab_def conflictfreeExt_def defends_def plusset_def stableExt_def stableLab_def undecset_def)

lemma stable_EL': "stableLab AF (Ext2Lab AF E) \<longrightarrow> stableExt AF E"
  unfolding stableExt_def stableLab_def range_def by (metis Ext2Lab_def admissibleExt_def completeAdmissible complete_EL')

(*semi-stable*)

lemma semistable_LE:  "semistableLab AF Lab \<longrightarrow> semistableExt AF (Lab2Ext Lab)"
  unfolding semistableExt_def semistableLab_def minimal_def maximal_def
  by (smt (verit, best) Ext2Lab_def Lab2Ext_def Label.exhaust completeLab2_def complete_EL complete_LE complete_defEq inset_def legallyOut_def outset_def plusset_def range_def undecset_def)

lemma semistable_LE': "semistableExt AF (Lab2Ext Lab) \<longrightarrow> semistable AF Lab"
  nitpick oops (*as expected*)

lemma semistable_EL:  "semistableExt AF E \<longrightarrow> semistableLab AF (Ext2Lab AF E)"
 unfolding semistableExt_def semistableLab_def minimal_def maximal_def
  by (smt (verit, ccfv_threshold) Ext2Lab_def Lab2Ext_def Label.distinct(3) Label.exhaust Label.simps(6) admissibleExt_def admissibleLab_def complete_EL complete_LE completeLab_def conflictfreeExt_def inset_def legallyOut_def outset_def plusset_def range_def undecset_def)

lemma semistable_EL': "semistableLab AF (Ext2Lab AF E) \<longrightarrow> semistableExt AF E"
  unfolding semistableExt_def semistableLab_def  minimal_def maximal_def
  by (smt (verit, ccfv_threshold) Ext2Lab_def Label.distinct(3) Label.simps(6) complete_EL complete_EL' range_def undecset_def)

(*stage*)

lemma stage_LE:  "stageLab AF Lab \<longrightarrow> stageExt AF (Lab2Ext Lab)" 
  unfolding stageExt_def stageLab_def minimal_def maximal_def range_def
  by (smt (verit) Ext2Lab_def Lab2Ext_def Label.distinct(5) Label.exhaust conflictfree_EL conflictfree_LE conflictfreeLab_def inset_def legallyOut_def outset_def plusset_def undecset_def)

lemma stage_LE': "stageExt AF (Lab2Ext Lab) \<longrightarrow> stageLab AF Lab"
  nitpick oops (*as expected*)

lemma stage_EL:  "stageExt AF E \<longrightarrow> stageLab AF (Ext2Lab AF E)"
  unfolding stageExt_def stageLab_def minimal_def maximal_def
  by (smt (verit, del_insts) Ext2Lab_def Lab2Ext_def Label.exhaust conflictfree_EL conflictfree_LE conflictfreeLab_def inset_def legallyOut_def outset_def plusset_def range_def undecset_def)

lemma stage_EL': "stageLab AF (Ext2Lab AF E) \<longrightarrow> stageExt AF E"
  unfolding stageExt_def stageLab_def minimal_def maximal_def range_def
  by (smt (verit, ccfv_threshold) Ext2Lab_def Label.distinct(3) Label.distinct(6) conflictfree_EL conflictfree_EL' undecset_def)

end
