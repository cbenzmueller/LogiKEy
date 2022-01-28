(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains labelling-based semantics for argumentation frameworks. *)
(* Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
*)
theory "labellings-simpl"
  imports "../base"
begin

(* The definitions below draw from [BCG 2011] but are stated for any arbitrarily labelled argument.
They are required to state the different definions for labellings semantics.*)

(* An argument is termed legally-in if all of its attackers are labelled out ([BCG 2011] Def. 9). *)
definition legallyIn :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>legallyIn AF Lab \<equiv> \<lambda>x.  (\<forall>y. (AF y x) \<longrightarrow> out Lab y)\<close>

(* An argument is termed legally-out if it has an in-labelled attacker ([BCG 2011] Def. 9). *)
definition legallyOut :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>legallyOut AF Lab \<equiv>  \<lambda>x.  (\<exists>y. (AF y x) \<and> in Lab y)\<close>

(* An argument is termed legally-undec if it is neither legally-in nor legally-out ([BCG2011] Def. 17). *)
definition legallyUndec :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>legallyUndec AF Lab \<equiv> \<lambda>x. \<not>legallyIn AF Lab x \<and> \<not>legallyOut AF Lab x\<close>

declare legallyIn_def[Defs] legallyOut_def[Defs] legallyUndec_def[Defs]

(***********************************************************)
(* Conflict-free labellings.                               *)
(***********************************************************)

(* A labelling is termed conflict-free when ([BCG2011] Def. 16)
 (i) every in-labelled argument is not legally-out (i.e. it does not have an attacked that is in-labelled);
(ii) every out-labelled argument is legally-out. *)  
definition conflictfreeLab :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>conflictfreeLab \<equiv> \<lambda>AF Lab. \<forall>x. (in Lab x  \<longrightarrow> \<not>legallyOut AF Lab x) \<and> (out Lab x \<longrightarrow> legallyOut AF Lab x)\<close>

(***********************************************************)
(* Admissible labellings.                                  *)
(***********************************************************)

(* A labelling is termed admissible when ([BCG2011] Def. 10)
 (i) every in-labelled argument is legally-in;
(ii) every out-labelled argument is legally-out. *) 
definition admissibleLab :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>admissibleLab \<equiv> \<lambda>AF Lab. \<forall>x. (in Lab x \<longrightarrow> legallyIn AF Lab x) \<and> (out Lab x \<longrightarrow> legallyOut AF Lab x)\<close>

(***********************************************************)
(* Complete labellings.                                    *)
(***********************************************************)

(* A complete labelling is an admissible labelling where every undec-labelled argument is legally-undec ([BCG2011] Def. 10). *)
definition completeLab :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>completeLab \<equiv> \<lambda>AF Lab. admissibleLab AF Lab \<and> (\<forall>x. undec Lab x \<longrightarrow> legallyUndec AF Lab x)\<close>

(* Complete labelling can be alternatively characterised as the labellings in which, for each argument A 
 (i) A is labelled in iff all its attackers are labelled out; and
(ii) A is labelled out iff it has at least one attacker that is labelled in ([BCG2011] Prop. 2). *)
definition completeLab2 :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>completeLab2 \<equiv> \<lambda>AF Lab. (\<forall>x. (in Lab x \<longleftrightarrow> legallyIn AF Lab x) \<and>
                                    (out Lab x \<longleftrightarrow> legallyOut AF Lab x))\<close>
(* for technical reasons this needs to be here *)
lemma complete_defEq: \<open>completeLab AF Lab = completeLab2 AF Lab\<close>
  by (smt (verit, del_insts) Label.distinct(3) Label.exhaust Label.simps(6) admissibleLab_def completeLab2_def completeLab_def inset_def legallyIn_def legallyOut_def legallyUndec_def outset_def undecset_def)


(***********************************************************)
(* Grounded labellings.                                    *)
(***********************************************************)

(* A grounded labelling is a (the) complete labelling whose in-set is minimal (least) wrt.
set inclusion ([BCG 2011] Def. 20). The two definitions below are shown equivalent in theory "tests". *)
definition groundedLab :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>groundedLab AF Lab \<equiv> minimal (completeLab AF) Lab in\<close>
definition groundedLab2 :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>groundedLab2 AF Lab \<equiv> least (completeLab AF) Lab in\<close>
 
(***********************************************************)
(* Preferred labellings.                                   *)
(***********************************************************)

(* Def. 22 from [BCG 2011] *)
definition preferredLab :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>preferredLab AF Lab \<equiv> maximal (completeLab AF) Lab in\<close>

(***********************************************************)
(* Ideal labellings.                                       *)
(***********************************************************)

(* Def. 28 from [BCG 2011] *)
definition lessOrEquallyCommittedLab :: \<open>'a Labelling \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> (infix "\<sqsubseteq>" 52) 
  where "L1 \<sqsubseteq> L2 \<equiv> (in(L1) \<subseteq> in(L2)) \<and> (out(L1) \<subseteq> out(L2))"
definition compatibleLab :: \<open>'a Labelling \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> (infix "\<asymp>" 52) 
  where "L1 \<asymp> L2 \<equiv> (in(L1) \<inter> out(L2)) \<approx> \<lbrace>-\<rbrace> \<and> (out(L1) \<inter> in(L2)) \<approx> \<lbrace>-\<rbrace>"
declare lessOrEquallyCommittedLab_def[Defs] compatibleLab_def[Defs]

lemma committedRefl: "L1 \<sqsubseteq> L1" by (simp add: lessOrEquallyCommittedLab_def)
lemma committedTrans: "L1 \<sqsubseteq> L2 \<and> L2 \<sqsubseteq> L3 \<longrightarrow> L1 \<sqsubseteq> L3" by (simp add: lessOrEquallyCommittedLab_def)
lemma committedAntisymm: "L1 \<sqsubseteq> L2 \<and> L2 \<sqsubseteq> L1 \<longleftrightarrow> L1 \<cong> L2" by (meson equivalentLab_def lessOrEquallyCommittedLab_def)

(* A quasi-ideal labelling is an admissible labelling that is
  less or equally commited than every preferred labelling: *)
definition qidealLab :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>qidealLab AF Lab \<equiv> admissibleLab AF Lab \<and> (\<forall>L. preferredLab AF L \<longrightarrow> Lab \<sqsubseteq> L)\<close>  

(* The ideal labelling of AF is the greatest/maximal quasi-ideal labelling
 wrt. relation \<sqsubseteq> (cf. [BCG 2011] Def. 29) *)
definition idealLab :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>idealLab AF Lab \<equiv> qidealLab AF Lab \<and> (\<forall>L. qidealLab AF L \<longrightarrow> L \<sqsubseteq> Lab)\<close>
definition idealLab2 :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>idealLab2 AF Lab \<equiv> qidealLab AF Lab \<and> (\<forall>L. qidealLab AF L \<and> Lab \<sqsubseteq> L \<longrightarrow> L \<cong> Lab)\<close> 

(* old (wrong) definition *)
definition idealOld :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>idealOld AF Lab \<equiv> admissibleLab AF Lab \<and> (\<forall>L. admissibleLab AF L \<longrightarrow> L \<sqsubseteq> Lab) \<and> (\<forall>L. preferredLab AF L \<longrightarrow> Lab \<sqsubseteq> L)\<close>  

(*old definition is stronger than the current one*)
lemma "idealOld AF Lab \<Longrightarrow> idealLab AF Lab" by (simp add: qidealLab_def idealOld_def idealLab_def)
lemma "idealLab AF Lab \<Longrightarrow> idealOld AF Lab"  oops

(*old definition entails the collapse of all preferred labellings*)
lemma "idealOld AF Lab \<Longrightarrow> \<forall>L. preferredLab AF L \<longrightarrow> L \<cong> Lab"
  by (smt (verit) completeLab_def equivalentLab_def idealOld_def lessOrEquallyCommittedLab_def maximal_def preferredLab_def)

(***********************************************************)
(* Stable labellings.                                      *)
(***********************************************************)

(* Def 24 from [BCG 2011] *)
definition stableLab :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>stableLab AF Lab \<equiv> completeLab AF Lab \<and> (\<forall>x. Lab(x) \<noteq> Undec)\<close>

(***********************************************************)
(* Semi-stable labellings.                                  *)
(***********************************************************)

(* Def. 26 from [BCG 2011] *) 
definition semistableLab :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>semistableLab AF Lab \<equiv> minimal (completeLab AF) Lab undec\<close>  

(***********************************************************)
(* Stage labellings.                                       *)
(***********************************************************)

(* Def. 31 from [BCG2011] *)
definition stageLab :: \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>stageLab AF Lab \<equiv> minimal (conflictfreeLab AF) Lab undec\<close> 

(* Technical: Include labellings into Defs collection *)
declare conflictfreeLab_def[Defs] admissibleLab_def[Defs] completeLab_def[Defs]
        completeLab2_def[Defs] groundedLab_def[Defs] groundedLab2_def[Defs]
        preferredLab_def[Defs] stableLab_def[Defs] semistableLab_def[Defs]
        qidealLab_def[Defs] idealLab_def[Defs]  stageLab_def[Defs]

end
