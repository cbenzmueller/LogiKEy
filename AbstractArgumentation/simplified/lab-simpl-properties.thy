theory "lab-simpl-properties"
  imports "labellings-simpl" "correspondence-simpl" "ext-simpl-properties"
begin

lemma DungFundLemma1Lab: "admissibleLab AF Lab \<Longrightarrow> \<forall>a. defends AF (Lab2Ext Lab) a \<longrightarrow> 
     admissibleLab AF (\<lambda>x. if (x = a) then In else (if (AF x a) then Out else Lab(x) ))"
  unfolding defends_def admissibleLab_def Lab2Ext_def  
  by (smt (verit, ccfv_threshold) Label.distinct(1) inset_def legallyIn_def legallyOut_def outset_def)

(******************** Admissible and conflict-free **********************)

(* There always exists an admissible Labelling (label, e.g., all arguments as Undec). *)
lemma exAdmissible: \<open>\<exists>Lab. admissibleLab AF Lab\<close> unfolding Defs by auto
(* See here: *)
lemma fixes AF :: \<open>'a Rel\<close> and Lab :: \<open>'a Labelling\<close>
      assumes \<open>\<forall>x. undec Lab x\<close> (* give every argument the label Undec *)
      shows \<open>admissibleLab AF Lab\<close> using assms unfolding Defs by simp

(* every admissible labelling is conflict-free but not the other way round*)
lemma admissibleConflictfree: \<open>admissibleLab AF Lab \<Longrightarrow> conflictfreeLab AF Lab\<close>
  by (simp add: admissibleLab_def conflictfreeLab_def inset_def legallyIn_def legallyOut_def outset_def)
lemma \<open>conflictfreeLab AF Lab \<Longrightarrow> admissibleLab AF Lab\<close> nitpick oops

(*For admissible labellings, legally-undecided implies undecided but not the other way round*)
lemma admissibleLegUndec: \<open>admissibleLab AF Lab \<Longrightarrow> legallyUndec AF Lab x \<longrightarrow> undec Lab x\<close>
  by (meson Label.exhaust admissibleLab_def inset_def legallyUndec_def outset_def undecset_def)
lemma \<open>admissibleLab AF Lab \<Longrightarrow> undec Lab x \<longrightarrow> legallyUndec AF Lab x\<close> nitpick oops

(*OTOH, for admissible labellings, legally-in/out still do not imply in/out*)
lemma \<open>admissibleLab AF Lab \<Longrightarrow> legallyIn AF Lab x \<longrightarrow> in Lab x\<close> nitpick oops
lemma \<open>admissibleLab AF Lab \<Longrightarrow> legallyOut AF Lab x \<longrightarrow> out Lab x\<close> nitpick oops


(********************************** Complete **************************************)
(* For complete labellings, legally-in/out does indeed imply in/out-labelled. *)
lemma completeLegIn:  \<open>completeLab AF Lab \<and> legallyIn AF Lab x \<longrightarrow> in Lab x\<close> unfolding Defs by (metis Label.exhaust)  
lemma completeLegOut: \<open>completeLab AF Lab \<and> legallyOut AF Lab x \<longrightarrow> out Lab x\<close> unfolding Defs by (metis Label.exhaust)  

(*in-sets of complete labellings are fixed points of the characteristic function*)
lemma completeInFP: "completeLab AF Lab \<Longrightarrow> fixpoint (\<F> AF) (in Lab)" 
  unfolding fixpoint_def by (metis completeLab2_def complete_defEq defends_def legallyIn_def legallyOut_def)

lemma \<open>\<exists>Lab. fixpoint (\<F> AF) (in Lab)\<close> unfolding fixpoint_def using complete_defEq exAdmissible oops (*TODO*)

(* complete labellings always exist *)
lemma completeExist: \<open>\<exists>Lab. completeLab AF Lab\<close> by (metis maxAdmissibleComplete maximal_def preferredExist preferredExt_def preferred_EL preferredLab_def)

(* every complete labelling is admissible but not the other way round *)
lemma completeAdmissible: \<open>completeLab AF Lab \<Longrightarrow> admissibleLab AF Lab\<close> by (simp add: completeLab_def)
lemma \<open>admissibleLab AF Lab \<Longrightarrow> completeLab AF Lab\<close> nitpick oops

(* For complete labellings we have that in/out-sets completely determine the labelling*)
lemma completeInLab: \<open>completeLab AF L1 \<Longrightarrow> completeLab AF L2 \<Longrightarrow> in(L1) \<approx> in(L2) \<longrightarrow> (\<forall>x. L1(x) = L2(x))\<close>
  by (smt (verit) Label.exhaust admissibleConflictfree completeLab_def conflictfreeLab_def inset_def legallyOut_def legallyUndec_def outset_def undecset_def)
lemma completeOutLab: \<open>completeLab AF L1 \<Longrightarrow> completeLab AF L2 \<Longrightarrow> out(L1) \<approx> out(L2) \<longrightarrow> (\<forall>x. L1(x) = L2(x))\<close>
  by (metis (full_types) Label.exhaust completeLab2_def complete_defEq inset_def legallyIn_def outset_def)
lemma \<open>completeLab AF L1 \<Longrightarrow> completeLab AF L2 \<Longrightarrow> undec(L1) \<approx> undec(L2) \<longrightarrow> (\<forall>x. L1(x) = L2(x))\<close> nitpick oops

(* For complete labellings, every in-set which is minimal is the least in-set.*)
lemma completeMinLeastIn: \<open>minimal (completeLab AF) Lab in \<longrightarrow> least (completeLab AF) Lab in\<close> oops (*TODO*)
(*(these two below may hold too, but are less important)*)
lemma \<open>minimal (completeLab AF) Lab out \<longrightarrow> least (completeLab AF) Lab out\<close> oops (*TODO*)
lemma \<open>maximal (completeLab AF) Lab undec \<longrightarrow> greatest (completeLab AF) Lab undec\<close> oops (*TODO*)

(*Lemma 1 from [BCG2011] *)
lemma Lemma1: \<open>completeLab AF Lab1 \<Longrightarrow> completeLab AF Lab2 \<Longrightarrow> (in(Lab1) \<subseteq> in(Lab2) \<longleftrightarrow> out(Lab1) \<subseteq> out(Lab2))\<close> unfolding Defs
  by (metis (full_types) Label.exhaust)

(*Prop 5 from [BCG2011], only partially proven so far *)
lemma prop5_1iff2: \<open>minimal (completeLab AF) Lab out = minimal (completeLab AF) Lab in\<close>
  unfolding minimal_def using complete_defEq completeLab2_def by (smt (z3) Label.exhaust legallyIn_def legallyOut_def)
(* some of the following still required *)
lemma prop5_1to3: \<open>minimal (completeLab AF) Lab in \<longrightarrow> maximal (completeLab AF) Lab undec\<close> oops (*TODO*)
lemma prop5_2to3: \<open>minimal (completeLab AF) Lab out \<longrightarrow> maximal (completeLab AF) Lab undec\<close> oops (*TODO*)
lemma prop5_3to1: \<open>maximal (completeLab AF) Lab undec \<longrightarrow> minimal (completeLab AF) Lab in\<close> oops (*TODO*)
lemma prop5_3to2: \<open>maximal (completeLab AF) Lab undec \<longrightarrow> minimal (completeLab AF) Lab out\<close> oops (*TODO*)

(*However, we can prove weaker variants of some of the above*)
lemma prop5_2to3_weak: \<open>least (completeLab AF) Lab out \<longrightarrow> greatest (completeLab AF) Lab undec\<close> unfolding least_def greatest_def
  by (smt (verit, best) Label.exhaust outset_def complete_defEq completeLab2_def undecset_def legallyIn_def inset_def)
lemma prop5_3to2_weak: \<open>greatest (completeLab AF) Lab undec \<longrightarrow> minimal (completeLab AF) Lab out\<close> unfolding minimal_def greatest_def
  by (metis admissibleConflictfree admissibleLegUndec completeLab_def completeLab2_def complete_defEq conflictfreeLab_def legallyUndec_def legallyOut_def)

(*Prop 8 from [BCG2011] 
 For complete labellings, being maximal/greatest wrt In is equivalent to being maximal/greatest wrt Out*)
lemma prop8: \<open>maximal (completeLab AF) Lab in \<longleftrightarrow> maximal (completeLab AF) Lab out\<close> unfolding maximal_def
  by (smt (z3) complete_defEq completeLab2_def legallyIn_def legallyOut_def)

lemma prop8': \<open>greatest (completeLab AF) Lab in \<longleftrightarrow> greatest (completeLab AF) Lab out\<close> unfolding greatest_def
  by (metis complete_defEq completeLab2_def legallyIn_def legallyOut_def)

(* In fact, being greatest wrt In implies being least wrt Undec, but not the other way round*)
lemma \<open>greatest (completeLab AF) Lab in \<longrightarrow> least (completeLab AF) Lab undec\<close> unfolding greatest_def least_def
  by (metis admissibleLegUndec completeLab_def completeLab2_def complete_defEq legallyOut_def legallyUndec_def)
lemma \<open>least (completeLab AF) Lab undec \<longrightarrow> greatest (completeLab AF) Lab in\<close> nitpick oops
(* Moreover, being minimal wrt Undec implies being maximal wrt In, but not the other way round (cf. semi-stable labellings)*)
lemma \<open>minimal (completeLab AF) Lab undec \<longrightarrow> maximal (completeLab AF) Lab in\<close> unfolding minimal_def maximal_def
  by (smt (verit, ccfv_SIG) Label.exhaust complete_defEq completeLab2_def inset_def legallyOut_def outset_def undecset_def)
lemma \<open>maximal (completeLab AF) Lab in \<longrightarrow> minimal (completeLab AF) Lab undec\<close> nitpick oops


(***************** Grounded ******************)

(* the two provided definitions of grounded labellings are equivalent *)
lemma grounded_defEq: \<open>groundedLab AF Lab = groundedLab2 AF Lab\<close> 
  unfolding groundedLab_def groundedLab2_def by (smt (verit) Lab2Ext_def complete_LE grounded_LE groundedLab_def groundedExt2_def groundedExt_defEq1 id_apply least_def minimal_def)

(* grounded labellings always exist *)
lemma grounded_exist: \<open>\<exists>Lab. groundedLab AF Lab\<close> 
  by (meson \<F>_leastFP_ex groundedExt3_def groundedExt_defEq1 groundedExt_defEq2 grounded_EL)

(* Side comment from [BCG2011] that grounded labellings are unique *)
lemma grounded_unique: \<open>groundedLab AF Lab1 \<Longrightarrow> groundedLab AF Lab2 \<Longrightarrow> \<forall>x. Lab1(x) = Lab2(x)\<close>
  unfolding grounded_defEq least_def 
  by (metis (full_types) completeInLab groundedLab2_def least_def)

(***************** Preferred ******************)

(* the following (naive) conjecture has a countermodel: *)
lemma "preferredLab AF Lab \<longleftrightarrow> maximal (admissibleLab AF) Lab in" nitpick oops

(* this works as an alternative definition for preferred labellings*)
lemma preferredMaxCompleteLabEq: "preferredLab AF Lab \<longleftrightarrow> completeLab AF Lab \<and> (\<forall>L. completeLab AF L \<and> Lab \<sqsubseteq> L \<longrightarrow> L \<cong> Lab)"
  unfolding preferredLab_def maximal_def using completeLab2_def complete_defEq 
  by (smt (verit, ccfv_threshold) equivalentLab_def legallyOut_def lessOrEquallyCommittedLab_def)

(* preferred labellings always exist *)
lemma preferredExist: \<open>\<exists>Lab. preferredLab AF Lab\<close> by (meson maxAdmissibleComplete preferredExist preferredExt_def preferred_EL)

(* Prop. 10 from [BCG2011] 
 If no argument is labelled Undec then the notions of conflict-free, admissible, complete and preferred collapse *)
lemma prop10_1to2: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> conflictfreeLab AF Lab \<longrightarrow> admissibleLab AF Lab\<close>
  unfolding Defs by (meson Label.exhaust)
lemma prop10_2to3: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> admissibleLab AF Lab \<longrightarrow> completeLab AF Lab\<close> 
  by (simp add: completeLab_def undecset_def)
lemma prop10_3to4: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> completeLab AF Lab \<longrightarrow>  preferredLab AF Lab\<close> unfolding preferredLab_def maximal_def
  by (metis admissibleConflictfree admissibleLegUndec completeLegIn completeLab_def conflictfreeLab_def legallyOut_def legallyUndec_def undecset_def)
lemma prop10_4to1: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> preferredLab AF Lab \<longrightarrow> conflictfreeLab AF Lab\<close>
  by (simp add: preferredLab_def admissibleConflictfree completeLab_def maximal_def)

(***************************** Ideal ************************)

lemma ideal_def_impl: \<open>idealLab AF Lab \<longrightarrow> idealLab2 AF Lab\<close> unfolding idealLab2_def idealLab_def 
  qidealLab_def preferredLab_def maximal_def using committedAntisymm by blast
lemma \<open>idealLab2 AF Lab \<longrightarrow> idealLab AF Lab\<close> oops (*TODO*)

(************************************* Stable, semi-stable and stage ************************)

(* the AF in which every arguments attacks itself does not have a stable labelling *)
lemma stableLem01: \<open>\<forall>Lab. \<not>stableLab (\<lambda>x y. x = y) Lab\<close>
  unfolding stableLab_def completeLab_def by (metis (mono_tags, hide_lams) Label.exhaust admissibleConflictfree conflictfreeLab_def legallyOut_def inset_def outset_def)

(* stable labellings do not exist necessarily *)
corollary \<open>\<exists>AF. \<forall>Lab. \<not>stableLab AF Lab\<close> using stableLem01 by auto

(*Lemma 14 from Dung. S is a stable extension iff S = {A | A is not attacked by S}.
Adapted to Labelings: It's weaker as we have to deal with Undec as well. *)
lemma lem14Dung: "stableLab AF Lab \<longrightarrow> (\<forall>a. in(Lab) a \<longleftrightarrow> \<not>(\<exists>b. in(Lab) b \<and> AF b a))" unfolding stableLab_def complete_defEq
  by (metis (full_types) Label.distinct(1) Label.exhaust completeLab2_def inset_def legallyOut_def outset_def)

(*Lemma 15 from Dung. Every stable extension is a preferred extension, but not vice versa.
Adapted to Labellings *)
lemma lem15Dung: \<open>stableLab AF Lab \<Longrightarrow> preferredLab AF Lab\<close> 
  by (simp add: prop10_3to4 stableLab_def)
lemma \<open>preferredLab AF Lab \<Longrightarrow> stableLab AF Lab\<close> nitpick[box=false] oops

(* semistable labellings always exist *)
lemma \<open>\<exists>Lab. semistableLab AF Lab\<close> oops (*TODO*)


end

