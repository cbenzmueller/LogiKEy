theory Tstit_Deontic_clean (*TDS logic*)
  imports Main
begin 

declare [[show_types]]
nitpick_params[user_axioms, show_all, format=2] (*global parameter setting for nitpick*) 

typedecl i (*possible world*)
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<gamma> = "\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<rho> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<delta> = "i\<Rightarrow>i\<Rightarrow>bool" (* type of accessibility relations between worlds *)

datatype ag = a1 | a2  (* dataype of mutually different agents; we provide 2, more can be added as needed *)

type_synonym \<omega> = "ag\<Rightarrow>i\<Rightarrow>i\<Rightarrow>bool"   (* type of agent dependent accessibility relations between worlds *)
type_synonym \<nu> = "(ag\<Rightarrow>bool)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>bool" (* type of set-of-agents dependent accessibility relations between worlds *)

consts 
  cw::i (*current world*)

  RBox::\<delta> (*worlds that are alternatives to each other: if (w, w1) then w1 is an alternative to w*)
  R_ag::\<omega> (*worlds that are actual choices for agent a, set of alternatives that are forced by agents i choice or action at world w*)
  R_set::\<nu> (*worlds that are actual choices for the set of agents Ag*)
  R_ag_ought::\<omega> (*set of alternatives that agent a ought to chose at moment m*)
 
  RG::\<delta> (*all worlds that are the strict future of world w: (w, w1) means that w1 is the strict future of w*)
  RH::\<delta> (*all worlds that are the strict past of world w: (w, w1) means that w1 is the strict past of w*)

  Ag::"ag\<Rightarrow>bool" (*set of all agents*)

definition Inv::"\<delta> \<Rightarrow> \<delta>" ("Inv _") where 
  "Inv R \<equiv> \<lambda>y x. R x y" 

lemma True nitpick [satisfy, user_axioms, show_all] oops (*empty assignment*) 

axiomatization where
  a1Set: "Ag a1" and
  a2Set: "Ag a2" 

axiomatization where
 (*reflexivity, symmetry, and transitivity for all equivalence relations*)
  accReR_ag:  "\<forall>a w. (R_ag a) w w" and
  accSymR_ag: "\<forall>a w v. (R_ag a) w v \<longrightarrow> (R_ag a) v w" and
  accTraR_ag: "\<forall>a w v u. ((R_ag a) w v \<and> (R_ag a) v u) \<longrightarrow> (R_ag a) w u" and

  accReRBox:  "\<forall>w. RBox w w" and
  accSymRBox: "\<forall>w v. RBox w v \<longrightarrow> RBox v w" and
  accTraRBox: "\<forall>w v u. (RBox w v \<and> RBox v u) \<longrightarrow> RBox w u" and

  accReR_set:  "\<forall>s w. (R_set s) w w" and
  accSymR_set: "\<forall>s w v. (R_set s) w v \<longrightarrow> (R_set s) v w" and
  accTraR_set: "\<forall>s w v u. ((R_set s) w v \<and> (R_set s) v u) \<longrightarrow> (R_set s) w u" and

  RG_serial: "(\<forall>x. (\<exists>y. (RG x y)))" and (*seriality of RG*)
  RG_trans: "(\<forall>x y z. (RG x y) \<and> (RG y z) \<longrightarrow> (RG x z))" and (*transitivity of RG*)
  Inv: "(Inv RG) = RH" and (*RH is the inverse of RG*)

  C1: "\<forall>a w1 w2. (R_ag a) w1 w2 \<longrightarrow> RBox w1 w2" and (*agents can only choose between alternatives*) 
  (*independence of agents/choices \<rightarrow> if w1 and w2 are alternatives to each other, there exists a world w which is 
  part of the actual choice of all agents \<rightarrow> see tests*)
  C2: "\<forall>w1 w2. (RBox w1 w2) \<longrightarrow> (\<exists>w. \<forall>a. (R_ag a) w1 w)" and
  (*independence of agents/choices \<rightarrow> if w1 and w2 are alternatives to each other, there exists a world w which is 
  part of the actual choice of all agents*)
  C3: "\<forall>S w1 w2. ((R_set S) w1 w2) \<longrightarrow> (\<forall>a. S a \<longrightarrow> (R_ag a) w1 w2)" and (*choices of agents in group Agt are 
  made up of the choices of the intersection of choices of each individual agent*) 
                           
  T4: "\<forall>u v w. ((RG w u) \<and> (RG w v)) \<longrightarrow> ((RG v u) \<or> (RG u v) \<or> u = v)" and (*future*)
  T5: "\<forall>u v w. ((RH w u) \<and> (RH w v)) \<longrightarrow> ((RH v u) \<or> (RH u v) \<or> u = v)" and (*past*)
  (* If v is in the future of w and u and v are in the same moment,  then there exists an alternative z 
  in the collective choice of all agents at w such that u is in the future of z.*)
  T6: "\<forall>v w u S. (RG w v) \<and> (RBox v u) \<longrightarrow> (\<exists>z. ((R_set S) w z) \<and> (RG z u))" and 
  T7: "\<forall>w v. ((RBox w v)) \<longrightarrow> \<not>(RG w v)" and (*if worlds are in the same moment, they can't be in each others future*)

  (*ideal worlds accessible at a moment are alternatives to the current world*)
  D8: "\<forall>a. \<forall>w v. ((R_ag_ought a) w v) \<longrightarrow> (RBox w v)" and
  (*at every moment for each agent there is a choice available that is an ideal choice*)
  D9: "\<forall>a. \<forall>w. (\<exists>v. (RBox w v) \<and> (\<forall>u. ((R_ag a) v u) \<longrightarrow> ((R_ag_ought a) w u)))" and 
  (*for each agent, if a world is ideal from the perspective of a particular world at a moment, that world is ideal from  
  the perspective of any world at that same moment, ideal worlds are settled upon moments*)
  D10: "\<forall>a. \<forall>w v u z. (RBox w v) \<and> (RBox w u) \<and> ((R_ag_ought a) u z) \<longrightarrow> ((R_ag_ought a) v z)" and 
  (*Every ideal world extends to a complete ideal choice, no choice contains both ideal and non-ideal worlds*)
  D11: "\<forall>a. \<forall>w v. ((R_ag_ought a) w v) \<longrightarrow> (\<exists>u. (RBox w u) \<and> ((R_ag a) u v) \<and> (\<forall>z. ((R_ag a) u z) \<longrightarrow> ((R_ag_ought a) w z)))"

  (*Logical connectives lifted*)
  abbreviation tdsNot::\<gamma> ("\<^bold>\<not>_") where "\<^bold>\<not>A \<equiv> \<lambda>w. \<not>A(w)" 
  abbreviation tdsAnd::\<rho> ("_\<^bold>\<and>_") where "A\<^bold>\<and>B \<equiv> \<lambda>w. A(w)\<and>B(w)"   
  abbreviation tdsOr::\<rho> ("_ \<^bold>\<or> _") where "A\<^bold>\<or>B \<equiv> \<lambda>w. A(w)\<or>B(w)"   
  abbreviation tdsImp::\<rho> ("_\<^bold>\<rightarrow>_") where "A\<^bold>\<rightarrow>B \<equiv> \<lambda>w. A(w)\<longrightarrow>B(w)"  
  abbreviation tdsEquiv::\<rho> ("_\<^bold>\<leftrightarrow>_") where "A\<^bold>\<leftrightarrow>B \<equiv> \<lambda>w. A(w)\<longleftrightarrow>B(w)"  
  abbreviation tdsBox::\<gamma> ("\<^bold>\<box>") where "\<^bold>\<box>A \<equiv> \<lambda>w. \<forall>v. A(v)" 
  abbreviation tdsDia::\<gamma> ("\<^bold>\<diamond>") where "\<^bold>\<diamond>A \<equiv> \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>A)"
  abbreviation tdsTop::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
  abbreviation tdsBot::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False" 

  (*Operators*)
  abbreviation tdsCstit::"ag\<Rightarrow>\<gamma>" ("[_] _") where "[i] A \<equiv> \<lambda>w. (\<forall>y. ((R_ag i) w y) \<longrightarrow> (A y))"  (*Chellas Stit*)
  abbreviation tdsCstitPoss::"ag\<Rightarrow>\<gamma>" ("<_>_") where "<i> A \<equiv> \<^bold>\<not>([i] (\<^bold>\<not> A))" (*Possibility Group Chellas stit*)
  abbreviation tdsCstitGr::"\<gamma>" ("[Ag]_") where "[Ag] A \<equiv> \<lambda>w. (\<forall>v. ((R_set Ag) w v) \<longrightarrow> (A v))" (*Chellas stit group*)
  abbreviation tdsCstitGrPoss::"\<gamma>" ("<Ag>_") where "<Ag> A \<equiv> \<^bold>\<not>([Ag] (\<^bold>\<not> A))"
  abbreviation tdsDstit::"ag\<Rightarrow>\<gamma>" ("[_]d _") where "[i]d A \<equiv> ([i]A) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<box>A)" (*Dstit*)
  abbreviation tdsDstitPoss::"ag\<Rightarrow>\<gamma>" ("<_>d _") where "<i>d A \<equiv> \<^bold>\<not> ([i]d (\<^bold>\<not> A))" (*Dstit Poss*)
  abbreviation tdsDstitGr::\<gamma> ("[Ag]d_") where "[Ag]d A \<equiv> ([Ag] A) \<^bold>\<and> (\<^bold>\<not>(\<^bold>\<box>A))" (*Dstit group*)
  abbreviation tdsDstitGrPoss::\<gamma> ("<Ag>d_") where "<Ag>d A \<equiv> \<^bold>\<not>([Ag]d(\<^bold>\<not> A))"
  abbreviation tdsOughtToDo::"ag\<Rightarrow>\<gamma>" ("\<^bold>\<otimes> _ _") where "\<^bold>\<otimes> i A \<equiv> \<lambda>w. (\<forall>v. ((R_ag_ought i) w v) \<longrightarrow> (A v))" (*OughtToDo Operator*)
  abbreviation tdsOughtToDoD::"ag\<Rightarrow>\<gamma>" ("\<^bold>\<otimes>d _ _") where "\<^bold>\<otimes>d i A \<equiv> (\<^bold>\<otimes> i A) \<^bold>\<and> (\<^bold>\<diamond> \<^bold>\<not> A)" (*OughtToDo Operator*) 

  abbreviation tdsG::\<gamma> ("G_") where "G A \<equiv> \<lambda>w. (\<forall>v. ((RG w v) \<longrightarrow> (A v)))" (*A will always be true in the future*)
  abbreviation tdsH::\<gamma> ("H_") where "H A \<equiv> \<lambda>w. (\<forall>v. ((RH w v) \<longrightarrow> (A v)))" (*A has always been true in the past*) 
  abbreviation tdsP::\<gamma> ("P_") where "P A \<equiv> \<^bold>\<not> (H (\<^bold>\<not> A))" (*it has not always been true that not A*)
  abbreviation tdsF::\<gamma> ("F_") where "F A \<equiv> \<^bold>\<not> (G (\<^bold>\<not> A))" (*it will not always be true that not A*)

  (*Validity*)
  abbreviation tdsValidLocal :: "(i\<Rightarrow>bool) \<Rightarrow> bool" ("\<Turnstile> _") where "\<Turnstile> A \<equiv> A cw"
  abbreviation tdsValidGlobal :: "(i \<Rightarrow> bool) \<Rightarrow> bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>A\<rfloor> \<equiv> \<forall>w. A w" 

lemma True nitpick [satisfy, user_axioms, show_all, finitize] oops

end


