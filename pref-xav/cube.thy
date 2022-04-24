section \<open>Base system E\<close>
(*<*)
theory cube
imports Main

begin
(*>*)


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



(*which is illustrated in Figure 1. In particular, proofs are
given for the equivalences of different axiomatizations and the 
inclusion relations shown in the cube.*)

section \<open>Framework\<close>

text \<open>This is Aqvis's system E from our 2019 IfColog paper.\<close>

typedecl i (*Possible worlds.*)
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<alpha> = "i\<Rightarrow>\<sigma>" (*Type of betterness relation between worlds.*)
type_synonym \<tau> = "\<sigma>\<Rightarrow>\<sigma>"


consts aw::i (*Actual world.*)  
abbreviation etrue  :: "\<sigma>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
abbreviation efalse :: "\<sigma>" ("\<^bold>\<bottom>")  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"   
abbreviation enot :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
abbreviation eand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
abbreviation eor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
abbreviation eimp :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
abbreviation eequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)" 

(*Possibilist--constant domain--quantification.*)
abbreviation eforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
abbreviation eforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation eexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
abbreviation eexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

abbreviation ebox :: "\<sigma>\<Rightarrow>\<sigma>" ("\<box>") where "\<box> \<equiv> \<lambda>\<phi> w.  \<forall>v. \<phi>(v)"  
definition ddediomond  :: "\<sigma>\<Rightarrow>\<sigma>" ("\<diamond>") where "\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. \<phi>(v)"

consts r :: "\<alpha>" (infixr "r" 70) (*Betterness relation, cf. def. of \<circle><_|_>.*)

(*Max rule *)

abbreviation emax  :: "\<sigma>\<Rightarrow>\<sigma>" ("max<_>")
  where "max<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> (x r v \<longrightarrow>  v r x)) )) )" 
abbreviation esubset :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infix "\<^bold>\<subseteq>" 53)
  where "\<phi> \<^bold>\<subseteq> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"
abbreviation econd  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<circle><_|_>")
  where "\<circle><\<psi>|\<phi>> \<equiv>  \<lambda>w. max<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation euncobl :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circle><_>")   
  where "\<^bold>\<circle><\<phi>> \<equiv> \<circle><\<phi>|\<^bold>\<top>>" 
abbreviation ddeperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("P<_|_>") 
  where "P<\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circle><\<^bold>\<not>\<psi>|\<phi>>"

(* opt rule*)

abbreviation eopt  :: "\<sigma>\<Rightarrow>\<sigma>" ("opt<_>")
  where "opt<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> v r x) )) )" 
abbreviation econdopt :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<odot><_|_>")
  where "\<odot><\<psi>|\<phi>> \<equiv>  \<lambda>w. opt<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation eperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<P><_|_>") 
  where "\<P><\<psi>|\<phi>> \<equiv> \<^bold>\<not>\<odot><\<^bold>\<not>\<psi>|\<phi>>"


(*David Lewis's evaluation rule for the conditional *)
abbreviation lewcond  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<otimes><_|_>")
  where "\<otimes><\<psi>|\<phi>> \<equiv> (\<lambda>v. (\<not>(\<exists>x. (\<phi>)(x))\<or>  (\<exists>x. ((\<phi>)(x)\<and>(\<psi>)(x) \<and> (\<forall>y. ((y r x) \<longrightarrow> (\<phi>)(y)\<longrightarrow>(\<psi>)(y)))))))"
definition lewperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<pi><_|_>") 
  where "\<pi><\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<otimes><\<^bold>\<not>\<psi>|\<phi>>"







abbreviation evalid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)  (*Global validity.*)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation ecjactual :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) (*Local validity — in world aw.*)  
  where "\<lfloor>p\<rfloor>\<^sub>l \<equiv> p(aw)"

lemma True nitpick [satisfy,user_axioms,expect=genuine] oops

subsection \<open>Properties\<close>

text \<open>We have the following constraints on the betterness relation\<close>

abbreviation reflexivity  where "reflexivity  \<equiv> (\<forall>x. x r x)"
abbreviation mlimitedness  where "mlimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. max<\<phi>>x))"
abbreviation msmoothness  where "msmoothness \<equiv> (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow> (max<\<phi>>x \<or> (\<exists>y. (y r x \<and> \<not>(x r y) \<and> max<\<phi>>y)))))"
abbreviation transitivity where "transitivity \<equiv> (\<forall>x y z. (x r y \<and> y r z) \<longrightarrow> x r z)"
abbreviation totalness where "totalness \<equiv> (\<forall>x y. (x r y \<or> y r x))"
abbreviation Ferrers where "Ferrers \<equiv> (\<forall>x y z u. ((x r u) \<and> (y r z)) \<longrightarrow> (x r z) \<or> (y r u))"

(* Some useful relations for constraining accessibility relations*)


definition transitive :: "\<alpha>\<Rightarrow>bool" where "transitive R \<equiv> \<forall>x y z. R x y \<and>  R y z \<longrightarrow> R x z"
definition sub_rel :: "\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" where "sub_rel R Q \<equiv> \<forall>u v. R u v \<longrightarrow> Q u v"
definition assfactor::"\<alpha>\<Rightarrow>\<alpha>" where "assfactor R \<equiv> \<lambda>u v. R u v \<and>\<not> R v u "



(*In HOL the transitive closure of a relation can be defined in a single line.*)
definition tc :: "\<alpha>\<Rightarrow>\<alpha>" where "tc R \<equiv> \<lambda>x y.\<forall>Q. transitive Q \<longrightarrow> (sub_rel R Q \<longrightarrow> Q x y)"


text \<open>We define Suzumura consistency:\<close>
abbreviation Suzumura
  where "Suzumura R \<equiv> \<forall>x y. (tc R x y \<longrightarrow> ( R y x \<longrightarrow> R x y))"

(* this is the  condition of a-cyclicity. Loops of pairs of strict betterness are ruled out *)

text \<open>We define a-cyciclicity TODO:\<close>

abbreviation loopfree
  where "loopfree R \<equiv> \<forall>x y. (tc assfactor R x y \<longrightarrow> ( R y x \<longrightarrow> R x y))"





subsection \<open>Correspondance under the max rule\<close>

text \<open>We go through the known correspondances, and verify them \<close>

text \<open>max-Limitedness corresponds to D\<close>

lemma assumes "mlimitedness"    
  shows  D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>\<rfloor>" sledgehammer oops (*proof found*)

lemma assumes D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>\<rfloor>"         
  shows "mlimitedness"   sledgehammer oops (*all timed out*)

text \<open>Smoothness corresponds to cautious monotony (CM)\<close>

lemma assumes "msmoothness"    
  shows  CM: "\<lfloor>(\<circle><\<psi>|\<phi>>\<^bold>\<and>\<circle><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" sledgehammer  oops (*proof found*)

lemma assumes CM: "\<lfloor>(\<circle><\<psi>|\<phi>>\<^bold>\<and>\<circle><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  shows  "msmoothness" sledgehammer oops  (* timed out*)

  text \<open>interval order (totalness plus Ferrers) corresponds to disjunctive rationality
 DR. The proof of completeness has not been published yet\<close>

lemma assumes "totalness"   
     (* assumes "Ferrers"*)
      shows  DR: "\<lfloor>\<circle><\<chi>|(\<phi>\<^bold>\<or>\<psi>)>\<^bold>\<rightarrow>((\<circle><\<chi>|\<phi>>\<^bold>)\<^bold>\<or>(\<circle><\<chi>|\<psi>>))\<rfloor>" sledgehammer  (*proof found*)
  
 lemma assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<circle><\<chi>|\<phi>>\<^bold>\<or>\<circle><\<chi>|\<psi>>)\<rfloor>" 
      shows "totalness" sledgehammer  oops (* timed out*)
lemma assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<or>\<psi>>\<^bold>\<rightarrow>(\<circle><\<chi>|\<phi>>\<or>\<circle><\<chi>|\<psi>>)\<rfloor>" 
      shows "Ferrers" sledgehammer   (* timed out*) oops


text \<open>Transitivity and totalness corresponds to the Spohn axiom (Sp)\<close>

lemma assumes "transitivity"    
      assumes "totalness"
      shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" sledgehammer oops
                                                                       (*proof found*)
lemma assumes  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
      shows "totalness" sledgehammer  oops (* timed out*)
lemma assumes  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
      shows "transitivity" sledgehammer   (* timed out*)

subsection \<open>Correspondance under the opt rule\<close>

text \<open>We move to the opt rule, and associate with it two news modal operators\<close>



text \<open>Here we redefine Lewis's limit assumption accordingly\<close>

abbreviation olimitedness  where "olimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x))"
abbreviation msmoothness  where "osmoothness \<equiv> (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow> (opt<\<phi>>x \<or> (\<exists>y. (y r x \<and> \<not>(x r y) \<and> opt<\<phi>>y)))))"

text \<open>Correspondance\<close>

text \<open>max-Limitedness corresponds to D\<close>

lemma assumes "mlimitedness"    
  shows  D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<odot><\<psi>|\<phi>> \<^bold>\<rightarrow> \<P><\<psi>|\<phi>>\<rfloor>" sledgehammer (*timed out*)

lemma assumes D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<odot><\<psi>|\<phi>> \<^bold>\<rightarrow> \<P><\<psi>|\<phi>>\<rfloor>"         
  shows "mlimitedness"   sledgehammer oops (*all timed out*)

text \<open>Smoothness corresponds to CM\<close>

lemma assumes "msmoothness"    
  shows  CM: "\<lfloor>(\<odot><\<psi>|\<phi>>\<^bold>\<and>\<odot><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<odot><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" sledgehammer  oops (*proof found*)

lemma assumes CM: "\<lfloor>(\<odot><\<psi>|\<phi>>\<^bold>\<and>\<odot><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<odot><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  shows  "msmoothness" sledgehammer oops  (* timed out*)

text \<open>interval order (totalness plus Ferrers) corresponds to DR\<close>

lemma assumes "totalness"   
     (* assumes "Ferrers"*)
      shows  DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<odot><\<chi>|\<phi>>\<^bold>\<or>\<odot><\<chi>|\<psi>>)\<rfloor>" sledgehammer oops (* timed out*)
  
 lemma assumes DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<odot><\<chi>|\<phi>>\<^bold>\<or>\<odot><\<chi>|\<psi>>)\<rfloor>" 
      shows "totalness" sledgehammer  oops (* timed out*)
lemma assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<or>\<psi>>\<^bold>\<rightarrow>(\<circle><\<chi>|\<phi>>\<or>\<circle><\<chi>|\<psi>>)\<rfloor>" 
      shows "Ferrers" sledgehammer   (* timed out*) oops




subsection \<open>Closure maximality and Lewis rule\<close>

(*ToDO*)

 text \<open>Under the Lewis rule, totalness corresponds to D \<close>

lemma
 assumes "totalness"
  shows D : "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<otimes><\<psi>|\<phi>> \<^bold>\<rightarrow>\<pi><\<psi>|\<phi>>)\<rfloor>" sledgehammer  oops(*proof found*)

lemma
  assumes  D : "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<otimes><\<psi>|\<phi>> \<^bold>\<rightarrow>\<pi><\<psi>|\<phi>>)\<rfloor>"
  shows "totalness" sledgehammer



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
      shows  Sp: "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" sledgehammer oops
                                                                       (*proof found*)
lemma assumes "transitivity"    
  shows  Trans: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<xi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<xi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>" sledgehammer oops
                                                                       (*the prover gave up*)
lemma assumes Sp: "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"
      assumes Trans: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<xi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<xi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"
      shows "transitivity"  sledgehammer 

  text \<open>Under the opt rule quasi-transitivity, a-cyclicity and Suzumura consistent do not correspond to 
any formula\<close>

(*to do*)

text \<open>Under the opt rule transitivity alone is equivalent to Sp and Trans\<close>
