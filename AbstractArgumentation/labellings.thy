(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains labelling-based semantics for argumentation frameworks. *)
(* Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
*)
theory labellings
  imports base
begin

(***********************************************************)
(* Preliminary notions.                                    *)
(***********************************************************)

(* The definitions below draw from [BCG 2011] but are stated for any arbitrarily labelled argument.
   They are required to state the different definitions for labellings semantics.*)

(* An argument is termed legally-in if all of its attackers are labelled out ([BCG 2011] Def. 9). *)
definition legallyIn :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> 'a \<Rightarrow> bool\<close> ("legallyIn\<^sup>_")
  where \<open>legallyIn\<^sup>\<A> att Lab \<equiv> \<lambda>x.  (\<forall>y. \<A> y \<longrightarrow> (att y x) \<longrightarrow> out Lab y)\<close>

(* An argument is termed legally-out if it has an in-labelled attacker ([BCG 2011] Def. 9). *)
definition legallyOut :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> 'a \<Rightarrow> bool\<close> ("legallyOut\<^sup>_")
  where \<open>legallyOut\<^sup>\<A> att Lab \<equiv>  \<lambda>x.  (\<exists>y. \<A> y \<and> (att y x) \<and> in Lab y)\<close>

(* An argument is termed legally-undec if it is neither legally-in nor legally-out ([BCG2011] Def. 17). *)
definition legallyUndec :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> 'a \<Rightarrow> bool\<close> ("legallyUndec\<^sup>_")
  where \<open>legallyUndec\<^sup>\<A> att Lab \<equiv> \<lambda>x. \<not>legallyIn\<^sup>\<A> att Lab x \<and> \<not>legallyOut\<^sup>\<A> att Lab x\<close>

(* Def. 28 from [BCG 2011] *)
definition lessOrEquallyCommittedLab :: \<open>'a Labelling \<Rightarrow> 'a Set \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("_\<sqsubseteq>\<^sup>__") 
  where "L1 \<sqsubseteq>\<^sup>\<A> L2 \<equiv> (in(L1) \<subseteq>\<^sup>\<A> in(L2)) \<and> (out(L1) \<subseteq>\<^sup>\<A> out(L2))"
definition compatibleLab :: \<open>'a Labelling \<Rightarrow> 'a Set \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("_\<asymp>\<^sup>__")
  where "L1 \<asymp>\<^sup>\<A> L2 \<equiv> (in(L1) \<inter> out(L2)) \<approx>\<^sup>\<A> \<lbrace>-\<rbrace> \<and> (out(L1) \<inter> in(L2)) \<approx>\<^sup>\<A> \<lbrace>-\<rbrace>"


(***********************************************************)
(* Conflict-free labellings.                               *)
(***********************************************************)

(* A labelling is termed conflict-free when ([BCG2011] Def. 16)
 (i) every in-labelled argument is not legally-out (i.e. it does not have an attacked that is in-labelled);
(ii) every out-labelled argument is legally-out. *)  
definition conflictfreeLab :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("conflictfreeLab\<^sup>_")
  where \<open>conflictfreeLab\<^sup>\<A> \<equiv> \<lambda>att Lab. \<forall>x. \<A> x \<longrightarrow> (in Lab x  \<longrightarrow> \<not>legallyOut\<^sup>\<A> att Lab x) \<and> (out Lab x \<longrightarrow> legallyOut\<^sup>\<A> att Lab x)\<close>


(***********************************************************)
(* Admissible labellings.                                  *)
(***********************************************************)

(* A labelling is termed admissible when ([BCG2011] Def. 10)
 (i) every in-labelled argument is legally-in;
(ii) every out-labelled argument is legally-out. *) 
definition admissibleLab :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("admissibleLab\<^sup>_")
  where \<open>admissibleLab\<^sup>\<A> \<equiv> \<lambda>att Lab. \<forall>x. \<A> x \<longrightarrow> (in Lab x \<longrightarrow> legallyIn\<^sup>\<A> att Lab x) \<and> (out Lab x \<longrightarrow> legallyOut\<^sup>\<A> att Lab x)\<close>


(***********************************************************)
(* Complete labellings.                                    *)
(***********************************************************)

(* A complete labelling is an admissible labelling where every undec-labelled argument is
   legally-undec ([BCG2011] Def. 10). *)
definition completeLab :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("completeLab\<^sup>_")
  where \<open>completeLab\<^sup>\<A> \<equiv> \<lambda>att Lab. admissibleLab\<^sup>\<A> att Lab \<and> (\<forall>x. \<A> x \<longrightarrow> undec Lab x \<longrightarrow> legallyUndec\<^sup>\<A> att Lab x)\<close>
 

(* Complete labelling can be alternatively characterised as the labellings in which, for each argument A 
 (i) A is labelled in iff all its attackers are labelled out; and
(ii) A is labelled out iff it has at least one attacker that is labelled in ([BCG2011] Prop. 2). *)
definition completeLab2 :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("completeLab2\<^sup>_")
  where \<open>completeLab2\<^sup>\<A> \<equiv> \<lambda>att Lab. (\<forall>x. \<A> x \<longrightarrow> (in Lab x \<longleftrightarrow> legallyIn\<^sup>\<A> att Lab x) \<and>
                                              (out Lab x \<longleftrightarrow> legallyOut\<^sup>\<A> att Lab x))\<close>

(* Both definitions, in fact, coincide: *)
lemma complete_defEq: \<open>completeLab\<^sup>\<A> att Lab \<longleftrightarrow> completeLab2\<^sup>\<A> att Lab\<close>
  by (smt (verit, ccfv_SIG) Label.exhaust Label.simps(3) Label.simps(5) admissibleLab_def
     completeLab2_def completeLab_def inset_def legallyIn_def legallyOut_def legallyUndec_def
      outset_def undecset_def)

(***********************************************************)
(* Grounded labellings.                                    *)
(***********************************************************)

(* A grounded labelling is a (the) complete labelling whose in-set is minimal (least) wrt. 
set inclusion ([BCG 2011] Def. 20). The two definitions below are shown equivalent in theory "tests". *)
definition groundedLab :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("groundedLab\<^sup>_")
  where \<open>groundedLab\<^sup>\<A> att Lab \<equiv> minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close>

definition groundedLab2 :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("groundedLab2\<^sup>_")
  where \<open>groundedLab2\<^sup>\<A> att Lab \<equiv> least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close>

(***********************************************************)
(* Preferred labellings.                                   *)
(***********************************************************)

(* Def. 22 from [BCG 2011] *)
definition preferredLab :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("preferredLab\<^sup>_")
  where \<open>preferredLab\<^sup>\<A> att Lab \<equiv> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close>

(***********************************************************)
(* Ideal labellings.                                       *)
(***********************************************************)

(* A quasi-ideal labelling is an admissible labelling that is
  less or equally commited than every preferred labelling: *)
definition qidealLab :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("qidealLab\<^sup>_")
  where \<open>qidealLab\<^sup>\<A> att Lab \<equiv> admissibleLab\<^sup>\<A> att Lab \<and> (\<forall>L. preferredLab\<^sup>\<A> att L \<longrightarrow> Lab \<sqsubseteq>\<^sup>\<A> L)\<close>  

(* The ideal labelling of AF is the greatest/maximal quasi-ideal labelling
 wrt. relation \<sqsubseteq> (cf. [BCG 2011] Def. 29) *)
definition idealLab :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("idealLab\<^sup>_")
  where \<open>idealLab\<^sup>\<A> att Lab \<equiv> qidealLab\<^sup>\<A> att Lab \<and> (\<forall>L. qidealLab\<^sup>\<A> att L \<longrightarrow> L \<sqsubseteq>\<^sup>\<A> Lab)\<close>
definition idealLab2 :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("idealLab2\<^sup>_")
  where \<open>idealLab2\<^sup>\<A> att Lab \<equiv> qidealLab\<^sup>\<A> att Lab \<and> (\<forall>L. qidealLab\<^sup>\<A> att L \<and> Lab \<sqsubseteq>\<^sup>\<A> L \<longrightarrow> L \<cong>\<^sup>\<A> Lab)\<close> 

(***********************************************************)
(* Stable labellings.                                      *)
(***********************************************************)

(* Def 24 from [BCG 2011] *)
definition stableLab :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("stableLab\<^sup>_")
  where \<open>stableLab\<^sup>\<A> att Lab \<equiv> completeLab\<^sup>\<A> att Lab \<and> (\<forall>x. \<A> x \<longrightarrow> Lab(x) \<noteq> Undec)\<close>

(***********************************************************)
(* Semi-stable labellings.                                 *)
(***********************************************************)

(* Def. 26 from [BCG 2011] *) 
definition semistableLab :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("semistableLab\<^sup>_")
  where \<open>semistableLab\<^sup>\<A> att Lab \<equiv> minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close>  

(***********************************************************)
(* Stage labellings.                                       *)
(***********************************************************)

(* Def. 31 from [BCG2011] *)
definition stageLab :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("stageLab\<^sup>_")
  where \<open>stageLab\<^sup>\<A> att Lab \<equiv> minimal\<^sup>\<A> (conflictfreeLab\<^sup>\<A> att) Lab undec\<close>  




(* Technical: Include labellings into Defs collection *)
declare legallyIn_def[Defs] legallyOut_def[Defs] legallyUndec_def[Defs]
        lessOrEquallyCommittedLab_def[Defs] compatibleLab_def[Defs]
declare conflictfreeLab_def[Defs] admissibleLab_def[Defs] completeLab_def[Defs]
        completeLab2_def[Defs] groundedLab_def[Defs] groundedLab2_def[Defs]
        preferredLab_def[Defs] idealLab_def[Defs]  stableLab_def[Defs]
        semistableLab_def[Defs] stageLab_def[Defs] 

end
