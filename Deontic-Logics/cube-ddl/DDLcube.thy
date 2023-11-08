theory DDLcube imports Main

begin

(*** We introduce Aqvist's system E from the 2019 IfColog paper ***)

typedecl i (* Possible worlds *)
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<alpha> = "i\<Rightarrow>\<sigma>" (* Type of betterness relation between worlds *)
type_synonym \<tau> = "\<sigma>\<Rightarrow>\<sigma>"


consts aw::i (* Actual world *)  
abbreviation etrue  :: "\<sigma>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
abbreviation efalse :: "\<sigma>" ("\<^bold>\<bottom>")  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"   
abbreviation enot :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
abbreviation eand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
abbreviation eor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
abbreviation eimpf :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
abbreviation eimpb :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftarrow>"49) where "\<phi>\<^bold>\<leftarrow>\<psi> \<equiv> \<lambda>w. \<psi>(w)\<longrightarrow>\<phi>(w)"  
abbreviation eequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)" 

abbreviation ebox :: "\<sigma>\<Rightarrow>\<sigma>" ("\<box>") where "\<box> \<equiv> \<lambda>\<phi> w.  \<forall>v. \<phi>(v)"  
abbreviation ddediomond  :: "\<sigma>\<Rightarrow>\<sigma>" ("\<diamond>") where "\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. \<phi>(v)"

abbreviation evalid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)  (* Global validity *)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation ecjactual :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) (* Local validity — in world aw *)  
  where "\<lfloor>p\<rfloor>\<^sub>l \<equiv> p(aw)"

consts r :: "\<alpha>" (infixr "\<^bold>r" 70) (* Betterness relation *)

abbreviation esubset :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infix "\<^bold>\<subseteq>" 53)
  where "\<phi> \<^bold>\<subseteq> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"

abbreviation eopt  :: "\<sigma>\<Rightarrow>\<sigma>" ("opt<_>")  (* opt rule*)
  where "opt<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> v \<^bold>r x) )) )" 
abbreviation econdopt :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<odot><_|_>")
  where "\<odot><\<psi>|\<phi>> \<equiv>  \<lambda>w. opt<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation eperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<P><_|_>") 
  where "\<P><\<psi>|\<phi>> \<equiv> \<^bold>\<not>\<odot><\<^bold>\<not>\<psi>|\<phi>>"

abbreviation emax  :: "\<sigma>\<Rightarrow>\<sigma>" ("max<_>")      (* Max rule *)
  where "max<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> (x \<^bold>r v \<longrightarrow>  v \<^bold>r x)) )) )" 
abbreviation econd  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<circle><_|_>")
  where "\<circle><\<psi>|\<phi>> \<equiv>  \<lambda>w. max<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation euncobl :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circle><_>")   
  where "\<^bold>\<circle><\<phi>> \<equiv> \<circle><\<phi>|\<^bold>\<top>>" 
abbreviation ddeperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("P<_|_>") 
  where "P<\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circle><\<^bold>\<not>\<psi>|\<phi>>"


(* Settings for model finder Nitpick *)

nitpick_params [user_axioms,show_all,expect=genuine] 


(*** First consistency check ***)

lemma True 
  nitpick [satisfy] (* model found *)
  oops

(*** The max-rule and opt-rule don't coincide ***)

lemma "\<odot><\<psi>|\<phi>> \<equiv> \<circle><\<psi>|\<phi>>" 
  nitpick [card i=1] (* counterexample found for card i=1 *) 
  oops

(* David Lewis's evaluation rule for the conditional *)

abbreviation lewcond :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("\<circ><_|_>")
  where "\<circ><\<psi>|\<phi>> \<equiv> \<lambda>v. (\<not>(\<exists>x. (\<phi>)(x))\<or>  
        (\<exists>x. ((\<phi>)(x)\<and>(\<psi>)(x) \<and> (\<forall>y. ((y \<^bold>r x) \<longrightarrow> (\<phi>)(y)\<longrightarrow>(\<psi>)(y))))))"
abbreviation lewperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<integral><_|_>") 
  where "\<integral><\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circ><\<^bold>\<not>\<psi>|\<phi>>"

(* Kratzer evaluation rule for the conditional *)

abbreviation kratcond :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("\<ominus><_|_>")
  where "\<ominus><\<psi>|\<phi>> \<equiv> \<lambda>v. ((\<forall>x. ((\<phi>)(x) \<longrightarrow> 
     (\<exists>y. ((\<phi>)(y)\<and>(y \<^bold>r x) \<and> ((\<forall>z. ((z \<^bold>r y) \<longrightarrow> (\<phi>)(z) \<longrightarrow> (\<psi>)(z)))))))))"
abbreviation kratperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<times><_|_>") 
  where "\<times><\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<ominus><\<^bold>\<not>\<psi>|\<phi>>"


(****************
Properties
******************)

(* The standard properties of the betterness relation *)

abbreviation "reflexivity  \<equiv> (\<forall>x. x \<^bold>r x)"
abbreviation "transitivity \<equiv> (\<forall>x y z. (x \<^bold>r y \<and> y \<^bold>r z) \<longrightarrow> x \<^bold>r z)"
abbreviation "totalness \<equiv> (\<forall>x y. (x \<^bold>r y \<or> y \<^bold>r x))"

(* 4 versions of Lewis's limit assumption *)

abbreviation "mlimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. max<\<phi>>x))"
abbreviation "msmoothness \<equiv> 
   (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow> (max<\<phi>>x \<or> (\<exists>y. (y \<^bold>r x \<and> \<not>(x \<^bold>r y) \<and> max<\<phi>>y)))))"
abbreviation "olimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x))"
abbreviation "osmoothness \<equiv> 
   (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow> (opt<\<phi>>x \<or> (\<exists>y. (y \<^bold>r x \<and> \<not>(x \<^bold>r y) \<and> opt<\<phi>>y)))))"

(* Weaker forms of transitivity--they require the notion of
transitive closure*)

definition transitive :: "\<alpha>\<Rightarrow>bool"
  where "transitive Rel \<equiv> \<forall>x y z. Rel x y \<and>  Rel y z \<longrightarrow> Rel x z"
definition sub_rel :: "\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" 
  where "sub_rel Rel1 Rel2 \<equiv> \<forall>u v. Rel1 u v \<longrightarrow> Rel2 u v"
definition assfactor::"\<alpha>\<Rightarrow>\<alpha>" 
  where "assfactor Rel \<equiv> \<lambda>u v. Rel u v \<and> \<not>Rel v u "

(* In HOL the transitive closure of a relation can be defined in a single line; here 
   we apply the construction to betterness relation \<^bold>r and for its strict 
   variant (\<lambda>u v. u \<^bold>r v \<and> \<not>v \<^bold>r u) *)
definition tcr  
  where "tcr \<equiv> \<lambda>x y. \<forall>Q. transitive Q \<longrightarrow> (sub_rel r Q \<longrightarrow> Q x y)"

definition tcr_strict
  where "tcr_strict \<equiv> \<lambda>x y. \<forall>Q. transitive Q \<longrightarrow> (sub_rel (\<lambda>u v. u \<^bold>r v \<and> \<not>v \<^bold>r u) Q \<longrightarrow> Q x y)"


(* Quasi-transitivity: the strict betterness
relation is transitive*)
abbreviation Quasitransit 
  where "Quasitransit  \<equiv> \<forall>x y z. (assfactor r x y \<and>  
                    assfactor r y z) \<longrightarrow> assfactor r x z"

(* Suzumura consistency: cycles with one 
non-strict betterness are ruled out*)
abbreviation Suzumura  
  where "Suzumura \<equiv> \<forall>x y. tcr x y \<longrightarrow> (y \<^bold>r x \<longrightarrow> x \<^bold>r y)"

theorem T1: "Suzumura \<equiv> \<forall>x y. tcr x y \<longrightarrow> \<not> (y \<^bold>r x \<and> \<not>x \<^bold>r y)" by simp

(* A-cyclicity: cycles of strict betterness are ruled out*)

abbreviation loopfree
  where "loopfree \<equiv> \<forall>x y. tcr_strict x y \<longrightarrow> (y \<^bold>r x \<longrightarrow> x \<^bold>r y)"

(* Interval order (reflexivity + Ferrers) *)
 
abbreviation Ferrers
  where "Ferrers \<equiv> (\<forall>x y z u. (x \<^bold>r u \<and> y \<^bold>r z) \<longrightarrow> (x \<^bold>r z \<or> y \<^bold>r u))"

theorem T2:
  assumes Ferrers and reflexivity  (*fact overlooked in the literature*)
  shows totalness
  by (simp add: assms(1) assms(2))  (* proof found *)


(*their relationships*)

theorem T3: '
  assumes transitivity 
  shows "Suzumura"
  by (metis assms sub_rel_def tcr_def transitive_def) 

theorem T4: 
  assumes transitivity 
  shows Quasitransit
  by (metis assfactor_def assms) 

theorem T5: 
  assumes Suzumura
  shows loopfree
  by (metis (no_types, lifting) assms sub_rel_def tcr_def tcr_strict_def) 

theorem T6: 
  assumes Quasitransit 
  shows loopfree
  sledgehammer
  by (smt (verit) assfactor_def assms sub_rel_def tcr_strict_def transitive_def) 
  
theorem T7: 
  assumes reflexivity and Ferrers 
  shows Quasitransit
  by (metis assfactor_def assms) 


(****************
Correspondance under the max rule 
******************)

(* Max-Limitedness corresponds to D *)

lemma "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>)\<rfloor>" 
  nitpick [card i=3]  (* counterexample found for card i=3 *) 
  oops 

lemma "\<lfloor>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"
  nitpick [card i=3]  (* counterexample found *)
  oops 

lemma "\<lfloor>\<circle><\<chi>|(\<phi>\<^bold>\<or>\<psi>)> \<^bold>\<rightarrow> ((\<circle><\<chi>|\<phi>>) \<^bold>\<or> (\<circle><\<chi>|\<psi>>))\<rfloor>"
  nitpick [card i=3]  (* counterexample found *)
  oops 

theorem T8: 
  assumes mlimitedness
  shows  "D*": "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>\<rfloor>"  
  sledgehammer
  using assms 
  oops

lemma 
  assumes "D*": "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<^bold>\<not>\<psi>|\<phi>>)\<rfloor>"
  shows mlimitedness 
  nitpick [card i=3]  (* counterexample found *)
  oops

(* Smoothness corresponds to cautious monotony *)

theorem T9: 
  assumes msmoothness    
  shows CM: "\<lfloor>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
sledgehammer
  using assms by force 

lemma 
  assumes CM: "\<lfloor>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"
  shows  msmoothness
  nitpick [card i=3]  (* counterexample found *)
  oops  

(*Interval order corresponds to disjunctive rationality*)

lemma 
  assumes reflexivity
  shows  DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  nitpick [card i=3]  (* counterexample found *)
  oops 

theorem T10: 
  assumes reflexivity and Ferrers
  shows  DR: "\<lfloor>\<circle><\<chi>|(\<phi>\<^bold>\<or>\<psi>)> \<^bold>\<rightarrow> (\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  sledgehammer
  by (metis assms) 
  
lemma 
  assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  shows reflexivity 
  nitpick [card i=1]  (* counterexample found *) 
  oops 

lemma 
  assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  shows Ferrers  
  nitpick [card i=2]  (* counterexample found *)
  oops 

(*Transitivity and totalness corresponds to the Spohn axiom (Sp)*)

lemma 
  assumes transitivity
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [card i=3] (* counterexample found *) 
  oops

lemma 
  assumes totalness 
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [card i=3] (* counterexample *) 
  oops

theorem T11: 
  assumes transitivity and totalness
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  by (metis assms)

theorem T12: 
  assumes transitivity and totalness
  shows  transit: "\<lfloor>( P<\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> P<\<psi>|\<psi>\<^bold>\<or>\<chi>>) \<^bold>\<rightarrow> P<\<phi>|(\<phi>\<^bold>\<or>\<chi>)>\<rfloor>" 
  by (metis assms(1) assms(2))
                                                          
lemma 
  assumes  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  shows totalness   
  nitpick [card i=1] (* counterexample found *) 
  oops

lemma 
  assumes  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  shows transitivity 
  nitpick [card i=2] (* counterexample found *) 
  oops 

(****************
Correspondance under the opt rule
******************)

(*opt-Limitedness corresponds to D*)

theorem T13: 
  assumes olimitedness   
  shows  D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<odot><\<psi>|\<phi>> \<^bold>\<rightarrow> \<P><\<psi>|\<phi>>\<rfloor>"   
  by (simp add: assms) 

lemma 
  assumes D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<odot><\<psi>|\<phi>> \<^bold>\<rightarrow> \<P><\<psi>|\<phi>>\<rfloor>"         
  shows olimitedness   
  nitpick [card i=1] (* counterexample found *)  
  oops 

(*Smoothness corresponds to cautious monotony*)

theorem T14: 
  assumes osmoothness   
  shows CM': "\<lfloor>( \<odot><\<psi>|\<phi>> \<^bold>\<and> \<odot><\<chi>|\<phi>> ) \<^bold>\<rightarrow> \<odot><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"   
  using assms by force 


lemma 
  assumes CM: "\<lfloor>( \<odot><\<psi>|\<phi>> \<^bold>\<and> \<odot><\<chi>|\<phi>> ) \<^bold>\<rightarrow> \<odot><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  shows  osmoothness 
  nitpick [card i=1] (* counterexample found  *)  
  oops
 

(*transitivity*)

theorem T15: 
  assumes transitivity   
  shows  Sp': "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
  by (metis assms) 

theorem T16: 
  assumes transitivity    
  shows  Trans: "\<lfloor>( \<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<psi>|\<psi>\<^bold>\<or>\<xi>> )\<^bold>\<rightarrow> \<P><\<phi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"   
  by (metis assms) 

lemma 
  assumes Sp: "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>> ) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"
  assumes Trans: "\<lfloor>( \<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<psi>|\<psi>\<^bold>\<or>\<xi>> ) \<^bold>\<rightarrow> \<P><\<phi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"
  shows transitivity    
  nitpick [card i=2] (* counterexample found  *)  
  oops 

(*interval order corresponds to disjunctive rationality*)

lemma 
  assumes reflexivity
     (* assumes "Ferrers"*)
  shows  DR': "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>"   
  nitpick [card i=3] (* counterexample found *)   
  oops 

theorem T17: 
  assumes reflexivity and Ferrers
  shows  DR': "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>"   
  by (metis assms(2))
 
lemma 
  assumes DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>" 
  shows reflexivity   
  nitpick [card i=1] (* counterexample found *)  
  oops 

lemma 
  assumes DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>" 
  shows Ferrers  
  nitpick [card i=2] (* counterexample found  *)  
  oops 

(****************
Relationship Lewis rule and max/opt rule 
*****************)

(* deontic explosion-max rule *)
theorem DEX: "\<lfloor>(\<diamond>\<phi> \<^bold>\<and> \<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<^bold>\<not>\<psi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>>\<rfloor>" 
  by blast  

(* no-deontic explosion-lewis rule *)
lemma DEX: "\<lfloor>(\<diamond>\<phi> \<^bold>\<and> \<circ><\<psi>|\<phi>> \<^bold>\<and> \<circ><\<^bold>\<not>\<psi>|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|\<phi>>\<rfloor>"
  nitpick [card i=2] (* counterexample  found*)
  oops

theorem T18:
  assumes mlimitedness and transitivity and totalness
  shows "\<lfloor>\<circ><\<psi>|\<phi>>\<^bold>\<leftrightarrow>\<odot><\<psi>|\<phi>>\<rfloor>"   
  sledgehammer
  by (smt (z3) assms)

theorem T19: 
  assumes mlimitedness and transitivity and totalness
  shows "\<lfloor>\<circ><\<psi>|\<phi>>\<^bold>\<leftrightarrow>\<circle><\<psi>|\<phi>>\<rfloor>" 
  sledgehammer
  by (smt (z3) assms) 



(****************
Correspondance Lewis evaluation rule for the conditional
*****************)

(* axioms of E holding if \<^bold>r transitive and total *)
lemma D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<integral><\<psi>|\<phi>>)\<rfloor>"  
  nitpick [card i=2] (* counterexample found *) 
  oops

theorem T20:
  assumes totalness
  shows D': "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<integral><\<psi>|\<phi>>)\<rfloor>" 
  by (metis assms)  

lemma Sp: "\<lfloor>( \<integral><\<psi>|\<phi>> \<^bold>\<and> \<circ><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [card i=3] (* counterexample found *) 
  oops 

theorem T21:
  assumes transitivity
  shows Sp'': "\<lfloor>( \<integral><\<psi>|\<phi>> \<^bold>\<and> \<circ><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"    
  using assms by blast 
   

lemma COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [card i=2] (* counterexample found *) 
  oops 

lemma
  assumes transitivity
  shows COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [card i=2] (* counterexample found *) 
  oops  

lemma 
  assumes totalness
  shows COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [card i=3] (* counterexample found *) 
  oops 
  
theorem T22:
  assumes transitivity and totalness
  shows COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
 by (smt (z3) assms) 


lemma CM: "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  nitpick [card i=2] (* counterexample found *) 
  oops 

lemma
  assumes transitivity
  shows CM: "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  nitpick [card i=2] (* counterexample found *) 
  oops 

lemma
  assumes totalness
  shows CM: "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  nitpick [card i=3] (* counterexample found *) 
  oops 

theorem T23:
  assumes transitivity and totalness
  shows CM'': "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  by (metis assms)  

lemma 
  assumes transitivity
  shows  transit: "\<lfloor>(\<times><\<phi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<and>\<times><\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> \<times><\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>" 
  nitpick [card i=1] (* counterexample found *)
  oops

lemma 
  assumes totalness
  shows  transit: "\<lfloor>(\<times><\<phi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<and>\<times><\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> \<times><\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>" 
  nitpick [card i=3] (* counterexample found *)
  oops

theorem T24:
  assumes transitivity and totalness
  shows  transit': "\<lfloor>(\<times><\<phi>|(\<phi>\<^bold>\<or>\<psi>)>\<^bold>\<and>\<times><\<psi>|(\<psi>\<^bold>\<or>\<chi>)>)\<^bold>\<rightarrow> \<times><\<phi>|(\<phi>\<^bold>\<or>\<chi>)>\<rfloor>" 
 by (smt (z3) assms) 
 

(*axioms of E holding irrespective of the properties of r*)

theorem Abs: "\<lfloor>\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<box>\<circ><\<psi>|\<phi>>\<rfloor>"  
  by blast  

theorem Nec: "\<lfloor>\<box>\<psi> \<^bold>\<rightarrow> \<circ><\<psi>|\<phi>>\<rfloor>" 
  by blast 

theorem Ext: "\<lfloor>\<box>(\<phi>\<^sub>1\<^bold>\<leftrightarrow>\<phi>\<^sub>2) \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>\<^sub>1> \<^bold>\<leftrightarrow> \<circ><\<psi>|\<phi>\<^sub>2>)\<rfloor>"
  by simp  

theorem Id: "\<lfloor>\<circ><\<phi>|\<phi>>\<rfloor>"
  by auto 

theorem  Sh: "\<lfloor>\<circ><\<psi>|\<phi>\<^sub>1\<^bold>\<and>\<phi>\<^sub>2> \<^bold>\<rightarrow> \<circ><(\<phi>\<^sub>2\<^bold>\<rightarrow>\<psi>)|\<phi>\<^sub>1>\<rfloor>"
  by blast 



section \<open>Negative results\<close>

text \<open>Under the max and opt rules there is no formula corresponding to reflexivity\<close>

(*ToDO not sure how to do it--something like there is no A such that "reflexivity <\<Rightarrow> A"*)

text \<open>Under the max and opt rules there is no formula corresponding to totalness\<close>

(*ToDO*)


text \<open>Under the max rule there is no formula corresponding to transitivity\<close>

(*ToDO*)


text \<open>Under the max rule there is no formula corresponding to a-cyclicity\<close>

(*ToDO*)


text \<open>Under the max rule there is no formula corresponding to Suzumura consistency\<close>

(*ToDO*)

text \<open>Under the Lewis rule there is no formula corresponding to limitedness/smoothness\<close>


section \<open>Some open problems\<close>

text \<open>Under the opt rule transitivity alone is equivalent to Sp and Trans\<close>

theorem T25:
  assumes transitivity 
  shows Sp''': "\<lfloor>\<forall>\<phi> \<psi> \<chi>. ( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
  by (metis assms) 

lemma 
  assumes "transitivity"    
  shows  Trans: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<xi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<xi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"   
  nitpick [card i=2] (* counterexample found for card i=2 *) 
  oops 

lemma 
  assumes Sp: "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"
          and  Trans: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<xi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<xi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"
  shows transitivity    
  nitpick [card i=2] (* counterexample found for card i=2 *) 
  oops 

  text \<open>Under the opt rule quasi-transitivity, a-cyclicity and Suzumura consistent do not correspond to 
any formula\<close>

(*to do*)

  text \<open>Under the opt rule transitivity alone is equivalent to Sp and Trans\<close>





(*attempt 1: the counter-model to rm is correct. tr holds for the values chosen for phi, psi and xi in the
counter-example, but can be falsified if we change them--see explanatory note*)


lemma 
  assumes tr: "\<lfloor>( P<\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> P<\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> P<\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>"
  shows rm: "\<lfloor> ( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [card i=3]
  
(*attempt 2: universal quantification on the propositions*)

lemma 
  assumes tr: "\<lfloor>\<forall>\<phi> \<psi> \<chi>. ( P<\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> P<\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> P<\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>"
  shows rm: "\<lfloor> \<forall>\<phi> \<psi> \<chi>.( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [card i=3] (* no proof state*)

end