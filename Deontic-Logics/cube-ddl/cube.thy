section \<open>Base system E\<close>

theory cube
imports Main

begin

subsection \<open>Introduction\<close>

subsection \<open>Base System E\<close>

text \<open>We present an approach to meta-reasoning about dyadic deontic logics, and
apply it to verify the relative strengths of logics in the deontic cube. This one is still
under construction, and closer to a line at the moment. We introduce the
properties of the betterness relation, and their syntactical counterparts. We ask Isabelle/HOL to

(1) confirm known correspondance (established by pen and paper) under
different evaluation rules for the conditional obligation operator: max rule, opt rule, closure 
maximality, and  Lewis rule.
(2) verify the asbsence of syntactical counterpart of some properties
(3) answer open problems regarding correspondance problems  (open in the sense of unsettled by
 pen and paper). \<close>


section \<open>Framework\<close>

text \<open>This is Aqvis's system E from the 2019 IfColog paper.\<close>

typedecl i  (* Possible worlds *)
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<alpha> = "i\<Rightarrow>\<sigma>" (* Type of betterness relation between worlds *)
type_synonym \<tau> = "\<sigma>\<Rightarrow>\<sigma>"


consts aw::i (*Actual world.*)  
abbreviation etrue  :: "\<sigma>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
abbreviation efalse :: "\<sigma>" ("\<^bold>\<bottom>")  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"   
abbreviation enot :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
abbreviation eand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
abbreviation eor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
abbreviation eimp :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
abbreviation eequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)" 

abbreviation ebox :: "\<sigma>\<Rightarrow>\<sigma>" ("\<box>") where "\<box> \<equiv> \<lambda>\<phi> w.  \<forall>v. \<phi>(v)"  
definition ddediomond  :: "\<sigma>\<Rightarrow>\<sigma>" ("\<diamond>") where "\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. \<phi>(v)"

abbreviation evalid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)  (* Global validity *)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation ecjactual :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) (* Local validity — in world aw *)  
  where "\<lfloor>p\<rfloor>\<^sub>l \<equiv> p(aw)"

consts r :: "\<alpha>" (infixr "r" 70) (* Betterness relation *)

abbreviation esubset :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infix "\<^bold>\<subseteq>" 53)
  where "\<phi> \<^bold>\<subseteq> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"

abbreviation eopt  :: "\<sigma>\<Rightarrow>\<sigma>" ("opt<_>")  (* opt rule*)
  where "opt<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> v r x) )) )" 
abbreviation econdopt :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<odot><_|_>")
  where "\<odot><\<psi>|\<phi>> \<equiv>  \<lambda>w. opt<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation eperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<P><_|_>") 
  where "\<P><\<psi>|\<phi>> \<equiv> \<^bold>\<not>\<odot><\<^bold>\<not>\<psi>|\<phi>>"

abbreviation emax  :: "\<sigma>\<Rightarrow>\<sigma>" ("max<_>")      (* Max rule *)
  where "max<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> (x r v \<longrightarrow>  v r x)) )) )" 
abbreviation econd  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<circle><_|_>")
  where "\<circle><\<psi>|\<phi>> \<equiv>  \<lambda>w. max<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation euncobl :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circle><_>")   
  where "\<^bold>\<circle><\<phi>> \<equiv> \<circle><\<phi>|\<^bold>\<top>>" 
abbreviation ddeperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("P<_|_>") 
  where "P<\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circle><\<^bold>\<not>\<psi>|\<phi>>"


nitpick_params [user_axioms,show_all,format=2,expect=genuine] (* Settings for model finder *)


lemma True (* Consistency check *)
  nitpick [satisfy] (* model found *)
  oops
 
lemma "\<odot><\<psi>|\<phi>> \<equiv> \<circle><\<psi>|\<phi>>" 
  nitpick [card i=1] (* counterexample found for card i=1*) 
  oops

text \<open>David Lewis's evaluation rule for the conditional\<close>

abbreviation lewcond :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("\<circ><_|_>")
  where "\<circ><\<psi>|\<phi>> \<equiv> \<lambda>v. (\<not>(\<exists>x. (\<phi>)(x))\<or>  
        (\<exists>x. ((\<phi>)(x)\<and>(\<psi>)(x) \<and> (\<forall>y. ((y r x) \<longrightarrow> (\<phi>)(y)\<longrightarrow>(\<psi>)(y))))))"
abbreviation lewperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<integral><_|_>") 
  where "\<integral><\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circ><\<^bold>\<not>\<psi>|\<phi>>"

text \<open>Kratzer evaluation rule for the conditional\<close>

abbreviation kratcond :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("\<ominus><_|_>")
  where "\<ominus><\<psi>|\<phi>> \<equiv> \<lambda>v. ((\<forall>x. ((\<phi>)(x)\<longrightarrow> (\<exists>y. ((\<phi>)(y)\<and>(y r x) \<and>( (\<forall>z. ((z r y) \<longrightarrow> (\<phi>)(z)\<longrightarrow>(\<psi>)(z)))))))))"
abbreviation kratperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<times><_|_>") 
  where "\<times><\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<ominus><\<^bold>\<not>\<psi>|\<phi>>"


lemma True (* Consistency check *)
  nitpick [satisfy,user_axioms,expect=genuine] (* model found *)
  oops

text \<open>The standard properties\<close>

abbreviation reflexivity  where "reflexivity  \<equiv> (\<forall>x. x r x)"
abbreviation transitivity 
  where "transitivity \<equiv> (\<forall>x y z. (x r y \<and> y r z) \<longrightarrow> x r z)"
abbreviation totalness 
  where "totalness \<equiv> (\<forall>x y. (x r y \<or> y r x))"

text \<open>4 versions of Lewis's limit assumption\<close>

abbreviation mlimitedness  
  where "mlimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. max<\<phi>>x))"
abbreviation msmoothness  
  where "msmoothness \<equiv> (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow>
                     (max<\<phi>>x \<or> (\<exists>y. (y r x \<and> \<not>(x r y) \<and> max<\<phi>>y)))))"
abbreviation olimitedness  
  where "olimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x))"
abbreviation osmoothness  where 
   "osmoothness \<equiv> (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow> 
                      (opt<\<phi>>x \<or> (\<exists>y. (y r x \<and> \<not>(x r y) \<and> opt<\<phi>>y)))))"
definition transitive :: "\<alpha>\<Rightarrow>bool" where "transitive R \<equiv> \<forall>x y z. R x y \<and>  R y z \<longrightarrow> R x z"
definition sub_rel :: "\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" where "sub_rel R Q \<equiv> \<forall>u v. R u v \<longrightarrow> Q u v"
definition assfactor::"\<alpha>\<Rightarrow>\<alpha>" where "assfactor R \<equiv> \<lambda>u v. R u v \<and> \<not> R v u "
(*In HOL the transitive closure of a relation can be defined in a single line.*)
definition tc :: "\<alpha>\<Rightarrow>\<alpha>" where "tc R \<equiv> \<lambda>x y.\<forall>Q. transitive Q \<longrightarrow> (sub_rel R Q \<longrightarrow> Q x y)"
(* this is a first form of a-cyclicity. Cycles with one non-strict betterness are ruled out*)
abbreviation Suzumura 
  where "Suzumura R \<equiv> \<forall>x y. (tc R x y \<longrightarrow> ( R y x \<longrightarrow> R x y))"
(* this is a second form of a-cyclicity. Cycles of non-strict betterness are ruled out*)
abbreviation loopfree
  where "loopfree R \<equiv> \<forall>x y. (tc (assfactor R) x y \<longrightarrow> ( R y x \<longrightarrow> R x y))"


text \<open>Interval order condition is totalness plus Ferrers\<close>

abbreviation Ferrers
  where "Ferrers \<equiv> (\<forall>x y z u. ((x r u) \<and> (y r z)) \<longrightarrow> (x r z) \<or> (y r u))"
lemma assumes Ferrers reflexivity  (*fact overlooked in the literature*)
  shows totalness
  sledgehammer (* proof found *) 
  by (simp add: assms(1) assms(2))  

lemma assumes "transitivity" 
  shows  transit: "\<lfloor>(\<times><\<phi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<and>\<times><\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> \<times><\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>" 
  nitpick [card i=1] (* counterexample found for card i=1 *)
  oops

lemma assumes "totalness" 
  shows  transit: "\<lfloor>(\<times><\<phi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<and>\<times><\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> \<times><\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>" 
  nitpick [card i=3] (* counterexample found for card i=3 *)
  oops

lemma assumes "transitivity" "totalness"
  shows  transit: "\<lfloor>(\<times><\<phi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<and>\<times><\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> \<times><\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>" 
  sledgehammer (* proof found *)
  (* by (metis assms(1) assms(2)) *)
  oops

text \<open>Max-Limitedness corresponds to D\<close>

lemma "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>)\<rfloor>" 
  nitpick [card i=3]  (* counterexample found for card i=3 *) 
  oops 

lemma "\<lfloor>(\<circle><\<psi>|\<phi>>\<^bold>\<and>\<circle><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"
  nitpick [card i=3]  (* counterexample found for card i=3 *)
  oops 

lemma "\<lfloor>\<circle><\<chi>|(\<phi>\<^bold>\<or>\<psi>)>\<^bold>\<rightarrow>((\<circle><\<chi>|\<phi>>)\<^bold>\<or>(\<circle><\<chi>|\<psi>>))\<rfloor>"
  nitpick [card i=3]  (* counterexample found for card i=3 *)
  oops 

lemma assumes "mlimitedness"
  shows  "D*": "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>\<rfloor>"  
  sledgehammer (* proof found *) 
  by (metis assms ddediomond_def) 

lemma assumes "D*": "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>(\<circle><\<psi>|\<phi>>\<^bold>\<and>\<circle><\<^bold>\<not>\<psi>|\<phi>>)\<rfloor>"
  shows "mlimitedness"   
  nitpick [card i=3]  (* counterexample found for card i=3 *)
  oops 

text \<open>Smoothness corresponds to cautious monotony\<close>

lemma assumes "msmoothness"    
  shows CM: "\<lfloor>(\<circle><\<psi>|\<phi>>\<^bold>\<and>\<circle><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  sledgehammer (* proof found *)
  using assms by force 

lemma assumes CM: "\<lfloor>(\<circle><\<psi>|\<phi>>\<^bold>\<and>\<circle><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"
  shows  "msmoothness" 
  nitpick [card i=3]  (* counterexample found for card i=3 *)
  oops  

text \<open>Interval order (reflexivity plus Ferrers) corresponds to disjunctive rationality\<close>

lemma assumes "reflexivity"
    (* assumes "Ferrers"*)
  shows  DR: "\<lfloor>\<circle><\<chi>|(\<phi>\<^bold>\<or>\<psi>)>\<^bold>\<rightarrow>((\<circle><\<chi>|\<phi>>)\<^bold>\<or>(\<circle><\<chi>|\<psi>>))\<rfloor>" 
  nitpick [card i=3]  (* counterexample found for card i=3 *)
  oops 

lemma assumes "reflexivity" "Ferrers"
  shows  DR: "\<forall>\<phi> \<psi> \<chi>.\<lfloor>\<circle><\<chi>|(\<phi>\<^bold>\<or>\<psi>)>\<^bold>\<rightarrow>((\<circle><\<chi>|\<phi>>)\<^bold>\<or>(\<circle><\<chi>|\<psi>>))\<rfloor>" 
  sledgehammer (* proof found *)
  by (metis assms(1) assms(2)) 
  
lemma assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<circle><\<chi>|\<phi>>\<^bold>\<or>\<circle><\<chi>|\<psi>>)\<rfloor>" 
  shows "reflexivity" 
  nitpick [card i=1]  (* counterexample found for card i=1 *) 
  oops 

lemma assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<circle><\<chi>|\<phi>>\<^bold>\<or>\<circle><\<chi>|\<psi>>)\<rfloor>" 
  shows "Ferrers"    
  nitpick [card i=2]  (* counterexample found for card i=2 *)
  oops 

text \<open>Transitivity and totalness corresponds to the Spohn axiom (Sp)\<close>

lemma assumes "transitivity"
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [card i=3] (* counterexample found for card i=3 *) 
  oops

lemma assumes "totalness" 
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [card i=3] (* counterexample for card i=3 *) 
  oops

lemma assumes "transitivity" "totalness"
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  sledgehammer (* proof found *)
  by (metis assms(1) assms(2)) 
                                                          
lemma assumes  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  shows "totalness"   
  nitpick [card i=1] (* counterexample found for card i=1 *) 
  oops 

lemma assumes  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  shows "transitivity" 
  nitpick [card i=2] (* counterexample found for card i=2 *) 
  oops 

subsection \<open>Correspondance under the opt rule\<close>

text \<open>We move to the opt rule, and associate with it two news modal operators\<close>
text \<open>Here we redefine Lewis's limit assumption accordingly\<close>
text \<open>Correspondance\<close>

text \<open>opt-Limitedness corresponds to D\<close>

lemma assumes "olimitedness"    
  shows  D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<odot><\<psi>|\<phi>> \<^bold>\<rightarrow> \<P><\<psi>|\<phi>>\<rfloor>"   
  sledgehammer (* proof found *)
  by (simp add: assms ddediomond_def) 

lemma assumes D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<odot><\<psi>|\<phi>> \<^bold>\<rightarrow> \<P><\<psi>|\<phi>>\<rfloor>"         
  shows "olimitedness"     
  nitpick [card i=1] (* counterexample found for card i=1 *)  
  oops 

text \<open>Smoothness corresponds to CM\<close>

lemma assumes "osmoothness"    
  shows CM': "\<lfloor>(\<odot><\<psi>|\<phi>>\<^bold>\<and>\<odot><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<odot><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"   
  sledgehammer (* proof found*)
  using assms by force 


lemma assumes CM: "\<lfloor>(\<odot><\<psi>|\<phi>>\<^bold>\<and>\<odot><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<odot><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  shows  "osmoothness"   
  nitpick [card i=1] (* counterexample found for card i=1 *)  
  oops
 

text \<open>Transitivity\<close>

lemma assumes "transitivity"    
  shows  Sp': "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
  sledgehammer (* proof found *) 
  by (metis assms) 

lemma assumes "transitivity"    
  shows  Trans: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<psi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<phi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"   
  sledgehammer (* proof found *)
  by (metis assms) 

lemma assumes Sp: "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"
  assumes Trans: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<psi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<phi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"
  shows "transitivity"    
  nitpick [card i=2] (* counterexample found for card i=2 *)  
  oops 

lemma assumes "totalness"
     (* assumes "Ferrers"*)
  shows  DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<odot><\<chi>|\<phi>>\<^bold>\<or>\<odot><\<chi>|\<psi>>)\<rfloor>"   
  nitpick [card i=3] (* counterexample found for card i=3 *)   
  oops 
  
 lemma assumes DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<odot><\<chi>|\<phi>>\<^bold>\<or>\<odot><\<chi>|\<psi>>)\<rfloor>" 
  shows "totalness"   
  nitpick [card i=1] (* counterexample found for card i=1 *)  
  oops 

lemma assumes DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<odot><\<chi>|\<phi>>\<^bold>\<or>\<odot><\<chi>|\<psi>>)\<rfloor>" 
  shows "Ferrers"   
  nitpick [card i=2] (* counterexample found for card i=2 *)  
  oops 


subsection \<open>Lewis rule\<close>
text \<open>Under the Lewis rule, totalness corresponds to D \<close>

(* deontic explosion-max rule *)
lemma DEX: "\<lfloor>(\<diamond>\<phi>\<^bold>\<and>\<circle><\<psi>|\<phi>>\<^bold>\<and>\<circle><\<^bold>\<not>\<psi>|\<phi>>)\<^bold>\<rightarrow> \<circle><\<chi>|\<phi>>\<rfloor>" 
  sledgehammer (*proof found*)
  by blast  

(* no-deontic explosion-lewis rule *)
lemma DEX: "\<lfloor>(\<diamond>\<phi>\<^bold>\<and>\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<^bold>\<not>\<psi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>>\<rfloor>"
  nitpick [card i=2] (* counterexample found for card i=2 *)  
  oops

lemma assumes "mlimitedness"
  assumes "transitivity" 
  assumes "totalness"
  shows "\<lfloor>\<circ><\<psi>|\<phi>>\<^bold>\<leftrightarrow>\<odot><\<psi>|\<phi>>\<rfloor>"
  sledgehammer (assms) (*proof found*)
  (* by (metis assms(1) assms(2) assms(3)) *) 
  oops

lemma assumes "mlimitedness"
  assumes "transitivity" 
  assumes "totalness"
  shows "\<lfloor>\<circ><\<psi>|\<phi>>\<^bold>\<leftrightarrow>\<circle><\<psi>|\<phi>>\<rfloor>"
  sledgehammer (assms) (* proof found *) 
  (* by (smt (verit) assms(1) assms(2) assms(3)) *)
  (* by (metis assms(1) assms(2) assms(3)) *) 
  oops

(* axioms of E holding if r transitive and total *)
lemma D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<integral><\<psi>|\<phi>>)\<rfloor>"  
  nitpick [card i=2] (* counterexample found for card i=2 *) 
  oops

lemma assumes "totalness"
  shows D': "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<integral><\<psi>|\<phi>>)\<rfloor>" 
  sledgehammer (* proof found *)
  by (metis assms ddediomond_def)  

lemma Sp: "\<lfloor>( \<integral><\<psi>|\<phi>> \<^bold>\<and> \<circ><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [card i=3] (* counterexample found for card i=3 *) 
  oops 

lemma assumes "transitivity"
  shows Sp'': "\<lfloor>( \<integral><\<psi>|\<phi>> \<^bold>\<and> \<circ><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
  sledgehammer (* proof found *) 
  using assms by blast 
   

lemma COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [card i=2] (* counterexample found for card i=2 *) 
  oops 

lemma
  assumes "transitivity" 
  shows COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [card i=2] (* counterexample found for card i=2 *) 
  oops  

  lemma 
  assumes "totalness"
  shows COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [card i=3] (* counterexample found for card i=3 *) 
  oops 
  
lemma 
  assumes "transitivity" 
  assumes "totalness"
  shows COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  sledgehammer (* proof found *) 
  by (smt (verit, ccfv_SIG) assms(1) assms(2)) 


lemma CM: "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  nitpick [card i=2] (* counterexample found for card i=2 *) 
  oops 

lemma
  assumes "transitivity"
  shows CM: "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  nitpick [card i=2] (* counterexample found for card i=2 *) 
  oops 

lemma
  assumes "totalness"
  shows CM: "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  nitpick [card i=3] (* counterexample found for card i=3 *) 
  oops 

lemma
  assumes "transitivity"
  assumes "totalness"
  shows CM'': "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  sledgehammer (assms) (* proof found *)
  by (metis assms(1) assms(2))  


(*axioms of E holding irrespective of the properties of r*)

lemma Abs:"\<lfloor>\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<box>\<circ><\<psi>|\<phi>>\<rfloor>"  
  sledgehammer (* proof found *)
  by blast  

lemma Nec:"\<lfloor>\<box>\<psi> \<^bold>\<rightarrow> \<circ><\<psi>|\<phi>>\<rfloor>"
  sledgehammer (* proof found *) 
  by blast 

lemma Ext:"\<lfloor>\<box>(\<phi>\<^sub>1\<^bold>\<leftrightarrow>\<phi>\<^sub>2) \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>\<^sub>1> \<^bold>\<leftrightarrow> \<circ><\<psi>|\<phi>\<^sub>2>)\<rfloor>"
  sledgehammer (* proof found *)
  by simp  

lemma Id:"\<lfloor>\<circ><\<phi>|\<phi>>\<rfloor>"
  sledgehammer (* proof found *) 
  by auto 

lemma Sh:"\<lfloor>\<circ><\<psi>|\<phi>\<^sub>1\<^bold>\<and>\<phi>\<^sub>2> \<^bold>\<rightarrow> \<circ><(\<phi>\<^sub>2\<^bold>\<rightarrow>\<psi>)|\<phi>\<^sub>1>\<rfloor>"
  sledgehammer (* proof found *) 
  by blast 


section \<open>Repugnant conclusion\<close>

text \<open>We verify the mere addition paradox\<close>
  







  
  
  
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

lemma assumes "transitivity"    
  shows Sp''': "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
  sledgehammer (* proof found *)
  by (metis assms) 

lemma assumes "transitivity"    
  shows  Trans: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<xi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<xi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"   
  nitpick [card i=2] (* counterexample found for card i=2 *) 
  oops 

lemma assumes Sp: "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"
      assumes Trans: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<xi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<xi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"
      shows "transitivity"    
  nitpick [card i=2] (* counterexample found for card i=2 *) 
  oops 

  text \<open>Under the opt rule quasi-transitivity, a-cyclicity and Suzumura consistent do not correspond to 
any formula\<close>

(*to do*)

text \<open>Under the opt rule transitivity alone is equivalent to Sp and Trans\<close>
end