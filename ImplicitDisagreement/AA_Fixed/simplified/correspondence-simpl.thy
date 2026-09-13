theory "correspondence-simpl"
  imports "extensions-simpl" "labellings-simpl"  "ext-simpl-properties"
begin

(**********************************************************)
(**** Correspondences between labellings and extensions ***)
(********** (including ideal semantics) *******************)
(**********************************************************)

(* Define mappings between extensions and labellings. *)
definition Lab2Ext::\<open>'a Labelling \<Rightarrow> 'a Set\<close>
  where \<open>Lab2Ext Lab \<equiv> in(Lab)\<close>
definition Ext2Lab::\<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Labelling\<close> (* Warning: works only for conflict-free sets! *)
  where \<open>Ext2Lab AF E \<equiv> \<lambda>a. if (E a) then In else (if ([AF|E]\<^sup>+ a) then Out else Undec)\<close>

(*conflict-free*)

lemma conflictfree_LE:  "conflictfreeLab AF Lab \<longrightarrow> conflictfreeExt AF (Lab2Ext Lab)" 
  by (metis (mono_tags, lifting) Lab2Ext_def conflictfreeExt_def conflictfreeLab_def legallyOut_def)

lemma conflictfree_LE': "conflictfreeExt AF (Lab2Ext Lab) \<longrightarrow> conflictfreeLab AF Lab"
  nitpick oops (*as expected*)

lemma conflictfree_EL:  "conflictfreeExt AF E \<longrightarrow> conflictfreeLab AF (Ext2Lab AF E)" 
  unfolding conflictfreeExt_def conflictfreeLab_def Ext2Lab_def
  by (smt (verit, best) Label.distinct(1) Label.distinct(3) Label.distinct(5) inset_def legallyOut_def outset_def plusset_def)

lemma conflictfree_EL': "conflictfreeLab AF (Ext2Lab AF E) \<longrightarrow> conflictfreeExt AF E"
  unfolding Ext2Lab_def conflictfreeExt_def conflictfreeLab_def by (simp add: inset_def legallyOut_def)

(*admissible*)

lemma admissible_LE:  "admissibleLab AF Lab \<longrightarrow> admissibleExt AF (Lab2Ext Lab)" 
  unfolding admissibleExt_def admissibleLab_def Lab2Ext_def
  by (metis (mono_tags, opaque_lifting) Label.distinct(1) defends_def conflictfreeExt_def inset_def legallyIn_def legallyOut_def outset_def)

lemma admissible_LE': "admissibleExt AF (Lab2Ext Lab) \<longrightarrow> admissibleLab AF Lab"
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

lemma complete_LE': "completeExt AF (Lab2Ext Lab) \<longrightarrow> completeLab AF Lab"
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

lemma preferred_LE': "preferredExt AF (Lab2Ext Lab) \<longrightarrow> preferredLab AF Lab"
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

lemma grounded_LE': "groundedExt AF (Lab2Ext Lab) \<longrightarrow> groundedLab AF Lab"
  nitpick oops (*as expected*)

lemma grounded_EL:  "groundedExt AF E \<longrightarrow> groundedLab AF (Ext2Lab AF E)"
  unfolding groundedExt_def groundedLab_def minimal_def
  by (metis Ext2Lab_def Lab2Ext_def Label.distinct(1) Label.distinct(3) complete_EL complete_LE id_def inset_def)

lemma grounded_EL': "groundedLab AF (Ext2Lab AF E) \<longrightarrow> groundedExt AF E"
  unfolding groundedExt_def groundedLab_def minimal_def
  by (smt (verit, del_insts) Ext2Lab_def Label.distinct(2) Label.distinct(3) complete_EL complete_EL' id_apply inset_def)

(* Ideal correspondences follow via quasi-ideal labellings and canonical conversion. *)

lemma canonical_in: "in (Ext2Lab AF E) = E"
  unfolding Ext2Lab_def inset_def by auto

lemma qideal_LE: "qidealLab AF Lab \<Longrightarrow> idealSet AF (Lab2Ext Lab)"
  unfolding qidealLab_def idealSet_def lessOrEquallyCommittedLab_def
  using admissible_LE preferred_EL canonical_in by (metis Lab2Ext_def)

lemma qideal_EL: "idealSet AF E \<Longrightarrow> qidealLab AF (Ext2Lab AF E)"
proof -
  assume ideal: "idealSet AF E"
  then have adm: "admissibleLab AF (Ext2Lab AF E)"
    using admissible_EL unfolding idealSet_def by blast
  have below: "Ext2Lab AF E \<sqsubseteq> L" if pref: "preferredLab AF L" for L
  proof -
    have sub: "E \<subseteq> in L"
      using ideal pref preferred_LE unfolding idealSet_def Lab2Ext_def by blast
    have comp: "completeLab AF L"
      using pref unfolding preferredLab_def maximal_def by blast
    show ?thesis
      using sub comp unfolding lessOrEquallyCommittedLab_def Ext2Lab_def
        complete_defEq completeLab2_def inset_def outset_def legallyOut_def plusset_def
      by auto
  qed
  show ?thesis using adm below unfolding qidealLab_def by blast
qed

lemma admissible_below_canonical:
  assumes "admissibleLab AF L" "conflictfreeExt AF E" "in L \<subseteq> E"
  shows "L \<sqsubseteq> Ext2Lab AF E"
  using assms unfolding admissibleLab_def conflictfreeExt_def
    lessOrEquallyCommittedLab_def Ext2Lab_def inset_def outset_def legallyOut_def plusset_def
  by (smt (verit) Label.distinct(1))

lemma ideal_LE: "idealLab AF Lab \<Longrightarrow> idealExt AF (Lab2Ext Lab)"
  unfolding idealLab_def idealExt_def greatest_def
  using qideal_LE qideal_EL canonical_in
  by (metis Lab2Ext_def id_apply lessOrEquallyCommittedLab_def)

lemma ideal_LE': "idealExt AF (Lab2Ext Lab) \<longrightarrow> idealLab AF Lab"
  nitpick oops (*as expected*)

lemma ideal_EL: "idealExt AF E \<longrightarrow> idealLab AF (Ext2Lab AF E)"
  unfolding idealExt_def greatest_def idealLab_def
  using qideal_EL qideal_LE admissible_below_canonical
  by (metis Lab2Ext_def admissibleExt_def id_apply idealSet_def qidealLab_def)

lemma ideal_EL': "idealLab AF (Ext2Lab AF E) \<longrightarrow> idealExt AF E"
  using ideal_LE canonical_in unfolding Lab2Ext_def by metis

lemma ideal_canonical:
  assumes ideal: "idealLab AF Lab"
  shows "Lab = Ext2Lab AF (Lab2Ext Lab)"
proof -
  have q: "qidealLab AF Lab" using ideal unfolding idealLab_def by blast
  have set: "idealSet AF (Lab2Ext Lab)" using qideal_LE q by blast
  have qcanon: "qidealLab AF (Ext2Lab AF (Lab2Ext Lab))"
    using qideal_EL set by blast
  have upper: "Ext2Lab AF (Lab2Ext Lab) \<sqsubseteq> Lab"
    using ideal qcanon unfolding idealLab_def by blast
  have lower: "Lab \<sqsubseteq> Ext2Lab AF (Lab2Ext Lab)"
    by (rule admissible_below_canonical)
      (use q set in \<open>auto simp: qidealLab_def idealSet_def admissibleExt_def Lab2Ext_def\<close>)
  show ?thesis using lower upper committedAntisymm equivLabId by blast
qed

(*stable*)

lemma stable_LE:  "stableLab AF Lab \<longrightarrow> stableExt AF (Lab2Ext Lab)"
  unfolding stableExt_def stableLab_def range_def
  by (metis (full_types) Lab2Ext_def Label.exhaust admissibleExt_def completeLab2_def completeExt_def complete_LE complete_defEq inset_def legallyIn_def outset_def plusset_def)

lemma stable_LE': "stableExt AF (Lab2Ext Lab) \<longrightarrow> stableLab AF Lab"
  nitpick oops (*as expected*)

lemma stable_EL:  "stableExt AF E \<longrightarrow> stableLab AF (Ext2Lab AF E)"
  by (smt (verit) range_def Ext2Lab_def Label.distinct(4) Label.distinct(6) admissibleExt_def admissible_EL completeLab_def conflictfreeExt_def defends_def plusset_def stableExt_def stableLab_def undecset_def)

lemma stable_EL': "stableLab AF (Ext2Lab AF E) \<longrightarrow> stableExt AF E"
  unfolding stableExt_def stableLab_def range_def by (metis Ext2Lab_def admissibleExt_def completeAdmissible complete_EL')

(*semi-stable*)

lemma semistable_LE:  "semistableLab AF Lab \<longrightarrow> semistableExt AF (Lab2Ext Lab)"
  unfolding semistableExt_def semistableLab_def minimal_def maximal_def
  by (smt (verit, best) Ext2Lab_def Lab2Ext_def Label.exhaust completeLab2_def complete_EL complete_LE complete_defEq inset_def legallyOut_def outset_def plusset_def range_def undecset_def)

(* A one-argument framework already refutes this converse. *)
lemma semistable_LE': "semistableExt AF (Lab2Ext (Lab :: unit Labelling)) \<longrightarrow> semistableLab AF Lab"
  nitpick[box=false, sat_solver=SAT4J] oops (*as expected*)

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
