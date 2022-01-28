(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains experiments with and verification of properties of labelling-based semantics
   for argumentation frameworks. *)
(* Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
 [Dung 1995] Dung, P.M., On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
            logic programming and n-person games, Artificial Intelligence. (1995)
*)
theory "lab-properties"
  imports labellings correspondence "ext-properties"
begin

(******************** Admissible and conflict-free **********************)

(* There always exists an admissible Labelling (label, e.g., all arguments as Undec). *)
lemma exAdmissible: \<open>\<exists>Lab. admissibleLab\<^sup>\<A> att Lab\<close> unfolding Defs by auto
(* See here: *)
lemma fixes att :: \<open>'a Rel\<close> and Lab :: \<open>'a Labelling\<close>
      assumes \<open>\<forall>x. \<A> x \<longrightarrow> undec Lab x\<close> (* give every argument the label Undec *)
      shows \<open>admissibleLab\<^sup>\<A> att Lab\<close> using assms unfolding Defs by simp

(* every admissible labelling is conflict-free but not the other way round*)
lemma admissibleLabConflictfree: \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> conflictfreeLab\<^sup>\<A> att Lab\<close> 
  by (simp add: admissibleLab_def conflictfreeLab_def inset_def legallyIn_def legallyOut_def outset_def)
lemma \<open>conflictfreeLab\<^sup>\<A> att Lab \<Longrightarrow> admissibleLab\<^sup>\<A> att Lab\<close> nitpick oops

(*For admissible labellings, legally-undecided implies undecided but not the other way round*)
lemma admissibleLabLegUndec: \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> legallyUndec\<^sup>\<A> att Lab x \<longrightarrow> undec Lab x\<close>
  unfolding admissibleLab_def by (meson Label.exhaust inset_def legallyUndec_def outset_def undecset_def)

lemma \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> undec Lab x \<longrightarrow> legallyUndec\<^sup>\<A> att Lab x\<close> nitpick oops

(*OTOH, for admissible labellings, legally-in/out still do not imply in/out*)
lemma \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> legallyIn\<^sup>\<A> att Lab x \<longrightarrow> in Lab x\<close> nitpick oops
lemma \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> legallyOut\<^sup>\<A> att Lab x \<longrightarrow> out Lab x\<close> nitpick oops

lemma DungFundLemma1Lab: \<open>admissibleLab\<^sup>\<A> att Lab \<and> defends\<^sup>\<A> att (in Lab) a \<longrightarrow>
                                admissibleLab\<^sup>\<A> att ( \<lambda>x. if (x = a) then In else
                                                     (if (att x a) then Out else (Lab x)) )\<close> 
  unfolding defends_rel_def admissibleLab_def
  by (smt (z3) Label.distinct(1) inset_def legallyIn_def legallyOut_def outset_def)
(********************************** Complete **************************************)

(* For complete labellings, legally-in/out does indeed imply in/out-labelled. *)
lemma completeLabLegIn:  \<open>completeLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> legallyIn\<^sup>\<A> att Lab x \<longrightarrow> in Lab x\<close>
  unfolding Defs using Label.exhaust by metis
lemma completeLabLegOut: \<open>completeLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> legallyOut\<^sup>\<A> att Lab x \<longrightarrow> out Lab x\<close>
  unfolding Defs using Label.exhaust by metis

(*in-sets of complete labellings are fixed points of the characteristic function*)
lemma completeLabInFP: "completeLab\<^sup>\<A> att Lab \<Longrightarrow> fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) (in Lab)"
  unfolding fixpoint_rel_def using completeLab2_def complete_defEq
  by (smt (verit, ccfv_threshold) defends_rel_def legallyIn_def legallyOut_def)

lemma completeLabInFP': "completeLab\<^sup>\<A> att Lab \<Longrightarrow> fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) (\<A> \<inter> (in Lab))"
unfolding fixpoint_rel_def using completeLab2_def complete_defEq
  by (smt (verit, ccfv_threshold) defends_rel_def legallyIn_def legallyOut_def)

(* lemma \<open>\<exists>Lab. fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) (in Lab)\<close> oops (*TODO*)  *)

(* complete labellings always exist *)
lemma \<open>\<exists>Lab. completeLab\<^sup>\<A> att Lab\<close> oops (*See adequacy.thy*) 

(* every complete labelling is admissible but not the other way round *)
lemma completeLabAdmissible: \<open>completeLab\<^sup>\<A> att Lab \<Longrightarrow> admissibleLab\<^sup>\<A> att Lab\<close> by (simp add: completeLab_def)
lemma \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> completeLab\<^sup>\<A> att Lab\<close> nitpick oops

(* For complete labellings we have that in/out-sets completely determine the labelling*)
lemma completeLabInLab: \<open>completeLab\<^sup>\<A> att L1 \<Longrightarrow> completeLab\<^sup>\<A> att L2 \<Longrightarrow> in(L1) \<approx>\<^sup>\<A> in(L2) \<longrightarrow> (\<forall>x. \<A> x \<longrightarrow> L1(x) = L2(x))\<close>
  unfolding completeLab2_def complete_defEq by (smt (verit, best) Label.exhaust inset_def legallyOut_def outset_def)

lemma completeLabOutLab: \<open>completeLab\<^sup>\<A> att L1 \<Longrightarrow> completeLab\<^sup>\<A> att L2 \<Longrightarrow> out(L1) \<approx>\<^sup>\<A> out(L2) \<longrightarrow> (\<forall>x. \<A> x \<longrightarrow> L1(x) = L2(x))\<close>
  unfolding completeLab2_def complete_defEq by (smt (verit, best) Label.exhaust inset_def legallyIn_def outset_def)

lemma \<open>completeLab\<^sup>\<A> att L1 \<Longrightarrow> completeLab\<^sup>\<A> att L2 \<Longrightarrow> undec(L1) \<approx>\<^sup>\<A> undec(L2) \<longrightarrow> (\<forall>x. \<A> x \<longrightarrow> L1(x) = L2(x))\<close> nitpick oops

(* For complete labellings, every in-set which is minimal is the least in-set.
(this result is key and has somehow to do with the fact that complete extensions are fixed points of a monotonic function)*)
lemma completeLabMinLeastIn: \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longrightarrow> least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close> 
  unfolding completeLab2_def complete_defEq using completeLabInFP oops (* nitpick oops (*TODO*) *)
(*(these two below may hold too, but are less important)*)
lemma \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out \<longrightarrow> least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close> oops
lemma \<open>maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close> oops

(*Lemma 1 from [BCG2011] *)
lemma \<open>completeLab\<^sup>\<A> att Lab1 \<Longrightarrow> completeLab\<^sup>\<A> att Lab2 \<Longrightarrow> ((in Lab1) \<subseteq>\<^sup>\<A> (in Lab2)) \<longleftrightarrow> ((out Lab1) \<subseteq>\<^sup>\<A> (out Lab2))\<close>
  unfolding Defs by (smt (verit) Label.exhaust inset_def legallyIn_def legallyOut_def legallyUndec_def outset_def)

(*Prop 5 from [BCG2011], only partially proven so far *)
lemma prop5_1iff2: \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out = minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close>
  unfolding minimal_rel_def using complete_defEq completeLab2_def by (smt (z3) Label.exhaust legallyIn_def legallyOut_def)

(* some of the following still required *)
lemma prop5_1to3: \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longrightarrow> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close> oops (*TODO*)
lemma prop5_2to3: \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out \<longrightarrow> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close> oops (*TODO*)
lemma prop5_3to1: \<open>maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close> oops (*TODO*)
lemma prop5_3to2: \<open>maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close> oops (*TODO*)

(*However, we can prove weaker variants of some of the above*)
lemma prop5_2to3_weak: \<open>least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out \<longrightarrow> greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close> 
  unfolding least_rel_def greatest_rel_def by (smt (verit, ccfv_SIG) Label.exhaust completeLab2_def complete_defEq inset_def legallyIn_def outset_def undecset_def)

lemma prop5_3to2_weak: \<open>greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close>
  unfolding minimal_rel_def greatest_rel_def 
  by (smt (verit, best) admissibleLabConflictfree Label.exhaust conflictfreeLab_def inset_def legallyOut_def outset_def undecset_def completeLabAdmissible)


(* Prop 2 BCG*)
lemma complete_iff_inoutlegal: \<open>completeLab\<^sup>\<A> att Lab \<longleftrightarrow> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = In) \<longleftrightarrow> \<forall>\<^sup>\<A> (\<lambda>b. att b a \<longrightarrow> (Lab b) = Out)) ) \<and> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = Out) \<longleftrightarrow> \<exists>\<^sup>\<A> (\<lambda>b. att b a \<and> (Lab b) = In)) )\<close>
proof
  show \<open>completeLab\<^sup>\<A> att Lab \<Longrightarrow> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = In) \<longleftrightarrow> \<forall>\<^sup>\<A> (\<lambda>b. att b a \<longrightarrow> (Lab b) = Out)) ) \<and> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = Out) \<longleftrightarrow> \<exists>\<^sup>\<A> (\<lambda>b. att b a \<and> (Lab b) = In)) )\<close>
  unfolding completeLab_def  admissibleLab_def
  by (smt (z3) Label.exhaust inset_def legallyIn_def legallyOut_def legallyUndec_def outset_def undecset_def) 
next
  show \<open> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = In) \<longleftrightarrow> \<forall>\<^sup>\<A> (\<lambda>b. att b a \<longrightarrow> (Lab b) = Out)) ) \<and> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = Out) \<longleftrightarrow> \<exists>\<^sup>\<A> (\<lambda>b. att b a \<and> (Lab b) = In)) ) \<Longrightarrow> completeLab\<^sup>\<A> att Lab\<close>
    by (smt (verit, del_insts) Label.distinct(3) Label.distinct(5) admissibleLab_def completeLab_def inset_def legallyIn_def legallyOut_def legallyUndec_def outset_def undecset_def)
qed


(*********************************** Grounded and Preferred ********************************)

(* the two provided definitions of grounded labellings are equivalent *)
lemma grounded_defEq: \<open>groundedLab\<^sup>\<A> att Lab \<longleftrightarrow> groundedLab2\<^sup>\<A> att Lab\<close>
  unfolding groundedLab_def groundedLab2_def
  by (smt (verit) Lab2Ext_def complete_LE grounded_LE groundedLab_def groundedExt2_def groundedExt_defEq1 id_apply least_rel_def minimal_rel_def)

(* grounded labellings always exist *)
lemma \<open>\<exists>Lab. groundedLab\<^sup>\<A> att Lab\<close> oops (*TODO*)

(* Side comment from [BCG2011] that grounded labellings are unique *)
lemma grounded_unique: \<open>groundedLab\<^sup>\<A> att Lab1 \<Longrightarrow> groundedLab\<^sup>\<A> att Lab2 \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> Lab1(x) = Lab2(x)\<close>
  unfolding grounded_defEq least_rel_def
  by (smt (verit, del_insts) completeLabInLab groundedLab2_def least_rel_def) 

(* preferred labellings always exist *)
lemma \<open>\<exists>Lab. preferredLab\<^sup>\<A> att Lab\<close> oops (*TODO*)


(************TODO **************)

(*Prop 8 from [BCG2011] 
 For complete labellings, being maximal/greatest wrt In is equivalent to being maximal/greatest wrt Out*)
lemma prop8: \<open>maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close> unfolding maximal_rel_def
  by (smt (z3) complete_defEq completeLab2_def legallyIn_def legallyOut_def)

lemma prop8': \<open>greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow> greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close> unfolding greatest_rel_def
  by (smt (z3) complete_defEq completeLab2_def legallyIn_def legallyOut_def)

(* In fact, being greatest wrt In implies being least wrt Undec, but not the other way round*)
lemma \<open>greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longrightarrow> least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close> unfolding greatest_rel_def least_rel_def
  by (smt (z3) admissibleLabLegUndec completeLab_def completeLab2_def complete_defEq legallyOut_def legallyUndec_def)

lemma \<open>least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close>  oops

(* Moreover, being minimal wrt Undec implies being maximal wrt In, but not the other way round (cf. semi-stable labellings)*)
lemma \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close> unfolding minimal_rel_def maximal_rel_def
  by (smt (verit, ccfv_SIG) Label.exhaust complete_defEq completeLab2_def inset_def legallyOut_def outset_def undecset_def)

lemma \<open>maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longrightarrow> minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close>  oops


(* Prop. 10 from [BCG2011] 
 If no argument is labelled Undec then the notions of conflict-free, admissible, complete and preferred collapse *)
lemma prop10_1to2: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> conflictfreeLab\<^sup>\<A> att Lab \<longrightarrow> admissibleLab\<^sup>\<A> att Lab\<close>
  by (smt (verit, ccfv_threshold) Label.exhaust inset_def admissibleLab_def conflictfreeLab_def legallyIn_def legallyOut_def outset_def)
lemma prop10_2to3: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> admissibleLab\<^sup>\<A> att Lab \<longrightarrow> completeLab\<^sup>\<A> att Lab\<close> 
  by (simp add: completeLab_def undecset_def)
lemma prop10_3to4: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> completeLab\<^sup>\<A> att Lab \<longrightarrow>  preferredLab\<^sup>\<A> att Lab\<close> unfolding preferredLab_def maximal_rel_def
  by (smt (verit, ccfv_SIG) Label.exhaust completeLab2_def complete_defEq inset_def legallyOut_def outset_def)
lemma prop10_4to1: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> preferredLab\<^sup>\<A> att Lab \<longrightarrow> conflictfreeLab\<^sup>\<A> att Lab\<close>
  by (simp add: preferredLab_def admissibleLabConflictfree completeLab_def maximal_rel_def)

(***************************** Ideal ************************)



(************************************* Stable, semi-stable and stage ************************)

(* the (nonempty) AF in which every arguments attacks itself does not have a stable labelling *)
lemma stableLem01: \<open>\<exists>x. \<A> x \<longrightarrow> (\<forall>Lab. \<not>stableLab\<^sup>\<A> (\<lambda>x y. x = y) Lab)\<close>
  unfolding stableLab_def completeLab_def by (metis (full_types) Label.exhaust admissibleLabConflictfree completeLab2_def completeLab_def complete_defEq conflictfreeLab_def inset_def legallyIn_def outset_def)

(* stable labellings do not exist necessarily *)
corollary \<open>\<exists>x. \<A> x \<longrightarrow> (\<exists>att. \<forall>Lab. \<not>stableLab\<^sup>\<A> att Lab)\<close> using stableLem01 by auto

(*Lemma 14 from Dung. S is a stable extension iff S = {A | A is not attacked by S}.
Adapted to Labelings: It's weaker as we have to deal with Undec as well. *)
lemma lem14Dung: "stableLab\<^sup>\<A> att Lab \<longrightarrow> (\<forall>a. \<A> a \<longrightarrow> (in(Lab) a \<longleftrightarrow> \<not>(\<exists>b. \<A> b \<and> in(Lab) b \<and> att b a)))" unfolding stableLab_def complete_defEq
  by (metis (full_types) Label.distinct(1) Label.exhaust completeLab2_def inset_def legallyOut_def outset_def)

(*Lemma 15 from Dung. Every stable extension is a preferred extension, but not vice versa.
Adapted to Labellings *)
lemma lem15Dung: \<open>stableLab\<^sup>\<A> att Lab \<Longrightarrow> preferredLab\<^sup>\<A> att Lab\<close>
  by (smt (verit, ccfv_SIG) completeLabAdmissible Lab2Ext_def admissibleLabConflictfree conflictfreeExt_def conflictfree_LE preferredLab_def stableLab_def lem14Dung maximal_rel_def)

lemma \<open>preferredLab\<^sup>\<A> att Lab \<Longrightarrow> stableLab\<^sup>\<A> att Lab\<close>  oops

(* semistable labellings always exist *)
lemma \<open>\<exists>Lab. semistableLab\<^sup>\<A> att Lab\<close> oops (*TODO*)




end

