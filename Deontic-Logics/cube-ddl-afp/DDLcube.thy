section \<open>Shallow Embedding and Meta-Logical Study of \AA qvist's system {\bf E}\<close>

text \<open>Maybe write some short introduction TODO ...\<close>

text \<open>We introduce Aqvist's system E from the 2019 IfColog paper \cite{J45}.\<close>

theory DDLcube imports Main  (*** Benzmueller/Parent 2024 ***)

begin  
nitpick_params [user_axioms,show_all,format=2] \<comment>\<open>Settings for model finder Nitpick\<close>

typedecl i \<comment>\<open>Possible worlds\<close>
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<alpha> = "i\<Rightarrow>\<sigma>" \<comment>\<open>Type of betterness relation between worlds\<close>
type_synonym \<tau> = "\<sigma>\<Rightarrow>\<sigma>"

consts aw::i \<comment>\<open>Actual world\<close>
abbreviation etrue  :: "\<sigma>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
abbreviation efalse :: "\<sigma>" ("\<^bold>\<bottom>")  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"   
abbreviation enot :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
abbreviation eand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
abbreviation eor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
abbreviation eimpf :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
abbreviation eimpb :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftarrow>"49) where "\<phi>\<^bold>\<leftarrow>\<psi> \<equiv> \<lambda>w. \<psi>(w)\<longrightarrow>\<phi>(w)"  
abbreviation eequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)" 

abbreviation ebox :: "\<sigma>\<Rightarrow>\<sigma>" ("\<box>") where "\<box>\<phi> \<equiv> \<lambda>w. \<forall>v. \<phi>(v)"  
abbreviation ddediomond  :: "\<sigma>\<Rightarrow>\<sigma>" ("\<diamond>") where "\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. \<phi>(v)"

abbreviation evalid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)  \<comment>\<open>Global validity\<close>
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation ecjactual :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) \<comment>\<open>Local validity — in world aw\<close>
  where "\<lfloor>p\<rfloor>\<^sub>l \<equiv> p(aw)"

consts r :: "\<alpha>" (infixr "\<^bold>r" 70) \<comment>\<open>Betterness relation\<close>

abbreviation esubset :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infix "\<^bold>\<subseteq>" 53)
  where "\<phi> \<^bold>\<subseteq> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"

abbreviation eopt  :: "\<sigma>\<Rightarrow>\<sigma>" ("opt<_>")  \<comment>\<open>opt rule\<close>
  where "opt<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> v \<^bold>r x) )) )" 
abbreviation econdopt :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<odot><_|_>")
  where "\<odot><\<psi>|\<phi>> \<equiv>  \<lambda>w. opt<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation eperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<P><_|_>") 
  where "\<P><\<psi>|\<phi>> \<equiv> \<^bold>\<not>\<odot><\<^bold>\<not>\<psi>|\<phi>>"

abbreviation emax  :: "\<sigma>\<Rightarrow>\<sigma>" ("max<_>")  \<comment>\<open>Max rule\<close>
  where "max<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> (x \<^bold>r v \<longrightarrow>  v \<^bold>r x)) )) )" 
abbreviation econd  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<circle><_|_>")
  where "\<circle><\<psi>|\<phi>> \<equiv>  \<lambda>w. max<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation euncobl :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circle><_>")   
  where "\<^bold>\<circle><\<phi>> \<equiv> \<circle><\<phi>|\<^bold>\<top>>" 
abbreviation ddeperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("P<_|_>") 
  where "P<\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circle><\<^bold>\<not>\<psi>|\<phi>>"

text \<open>First consistency check:\<close>

lemma True 
  nitpick [satisfy] \<comment>\<open>model found\<close>
  oops

text \<open>The max-rule and opt-rule don't coincide:\<close>

lemma "\<odot><\<psi>|\<phi>> \<equiv> \<circle><\<psi>|\<phi>>" 
  nitpick [card i=1] \<comment>\<open>counterexample found for card i=1\<close>
  oops

text \<open>David Lewis's evaluation rule for the conditional:\<close>

abbreviation lewcond :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("\<circ><_|_>")
  where "\<circ><\<psi>|\<phi>> \<equiv> \<lambda>v. (\<not>(\<exists>x. (\<phi>)(x))\<or>  
        (\<exists>x. ((\<phi>)(x)\<and>(\<psi>)(x) \<and> (\<forall>y. ((y \<^bold>r x) \<longrightarrow> (\<phi>)(y)\<longrightarrow>(\<psi>)(y))))))"
abbreviation lewperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<integral><_|_>") 
  where "\<integral><\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circ><\<^bold>\<not>\<psi>|\<phi>>"

text \<open>Kratzer evaluation rule for the conditional:\<close>

abbreviation kratcond :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("\<ominus><_|_>")
  where "\<ominus><\<psi>|\<phi>> \<equiv> \<lambda>v. ((\<forall>x. ((\<phi>)(x) \<longrightarrow> 
     (\<exists>y. ((\<phi>)(y)\<and>(y \<^bold>r x) \<and> ((\<forall>z. ((z \<^bold>r y) \<longrightarrow> (\<phi>)(z) \<longrightarrow> (\<psi>)(z)))))))))"
abbreviation kratperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<times><_|_>") 
  where "\<times><\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<ominus><\<^bold>\<not>\<psi>|\<phi>>"


subsection \<open>Properties\<close>

text \<open>The standard properties of the betterness relation:\<close>

abbreviation "reflexivity  \<equiv> (\<forall>x. x \<^bold>r x)"
abbreviation "transitivity \<equiv> (\<forall>x y z. (x \<^bold>r y \<and> y \<^bold>r z) \<longrightarrow> x \<^bold>r z)"
abbreviation "totality \<equiv> (\<forall>x y. (x \<^bold>r y \<or> y \<^bold>r x))"

text \<open>4 versions of Lewis's limit assumption:\<close>

abbreviation "mlimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. max<\<phi>>x))"
abbreviation "msmoothness \<equiv> 
   (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow> (max<\<phi>>x \<or> (\<exists>y. (y \<^bold>r x \<and> \<not>(x \<^bold>r y) \<and> max<\<phi>>y)))))"
abbreviation "olimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x))"
abbreviation "osmoothness \<equiv> 
   (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow> (opt<\<phi>>x \<or> (\<exists>y. (y \<^bold>r x \<and> \<not>(x \<^bold>r y) \<and> opt<\<phi>>y)))))"

text \<open>Weaker forms of transitivity — they require the notion of
transitive closure.\<close>

definition transitive :: "\<alpha>\<Rightarrow>bool"
  where "transitive Rel \<equiv> \<forall>x y z. Rel x y \<and>  Rel y z \<longrightarrow> Rel x z"
definition sub_rel :: "\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" 
  where "sub_rel Rel1 Rel2 \<equiv> \<forall>u v. Rel1 u v \<longrightarrow> Rel2 u v"
definition assfactor::"\<alpha>\<Rightarrow>\<alpha>" 
  where "assfactor Rel \<equiv> \<lambda>u v. Rel u v \<and> \<not>Rel v u "

text \<open>In HOL the transitive closure of a relation can be defined in a single line; 
here we apply the construction to the betterness relation and its strict variant.\<close>

definition tcr  
  where "tcr \<equiv> \<lambda>x y. \<forall>Q. transitive Q \<longrightarrow> (sub_rel r Q \<longrightarrow> Q x y)"

definition tcr_strict
  where "tcr_strict \<equiv> \<lambda>x y. \<forall>Q. transitive Q 
                               \<longrightarrow> (sub_rel (\<lambda>u v. u \<^bold>r v \<and> \<not>v \<^bold>r u) Q \<longrightarrow> Q x y)"

text \<open>Quasi-transitivity: the strict betterness relation is transitive\<close>

abbreviation Quasitransit 
  where "Quasitransit  \<equiv> \<forall>x y z. (assfactor r x y \<and>  
                    assfactor r y z) \<longrightarrow> assfactor r x z"

text \<open>Suzumura consistency: cycles with one non-strict betterness are ruled out.\<close>

abbreviation Suzumura  
  where "Suzumura \<equiv> \<forall>x y. tcr x y \<longrightarrow> (y \<^bold>r x \<longrightarrow> x \<^bold>r y)"

theorem T1: "Suzumura \<equiv> \<forall>x y. tcr x y \<longrightarrow> \<not> (y \<^bold>r x \<and> \<not> (x \<^bold>r y))" by simp

text \<open>A-cyclicity: cycles of strict betterness are ruled out.\<close>

abbreviation loopfree
  where "loopfree \<equiv> \<forall>x y. tcr_strict x y \<longrightarrow> (y \<^bold>r x \<longrightarrow> x \<^bold>r y)"

text \<open>Interval order (reflexivity + Ferrers):\<close>
 
abbreviation Ferrers
  where "Ferrers \<equiv> (\<forall>x y z u. (x \<^bold>r u \<and> y \<^bold>r z) \<longrightarrow> (x \<^bold>r z \<or> y \<^bold>r u))"

theorem T2:
  assumes Ferrers and reflexivity  \<comment>\<open>fact overlooked in the literature\<close>
  shows totality
  \<comment>\<open>sledgehammer\<close>
  by (simp add: assms(1) assms(2)) 

text \<open>Study of relationships:\<close>

theorem T3: 
  assumes transitivity 
  shows "Suzumura"
  \<comment>\<open>sledgehammer\<close>
  by (metis assms sub_rel_def tcr_def transitive_def)
 
theorem T4:
  assumes transitivity 
  shows Quasitransit
  \<comment>\<open>sledgehammer\<close>
  by (metis assfactor_def assms) 

theorem T5:
  assumes Suzumura
  shows loopfree
  \<comment>\<open>sledgehammer\<close>
  by (metis (no_types, lifting) assms sub_rel_def tcr_def tcr_strict_def)

theorem T6: 
  assumes Quasitransit 
  shows loopfree
  \<comment>\<open>sledgehammer\<close>
  by (smt (verit, best) assfactor_def assms sub_rel_def tcr_strict_def transitive_def)

theorem T7: 
  assumes reflexivity and Ferrers 
  shows Quasitransit
  by (metis assfactor_def assms) 

subsection \<open>Tests: max rule\<close>

text \<open>Inference rules\<close>

lemma MP: "\<lbrakk>\<lfloor>\<phi>\<rfloor>; \<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>\<psi>\<rfloor>" by simp
lemma NEC: "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<box>\<phi>\<rfloor>" by simp

text \<open>@{term "\<box>"} is an S5 modality\<close>

lemma C_1_refl: "\<lfloor>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>" by simp
lemma C_1_trans: "\<lfloor>\<box>\<phi> \<^bold>\<rightarrow> (\<box>(\<box>\<phi>))\<rfloor>"  by simp
lemma C_1_sym: "\<lfloor>\<phi> \<^bold>\<rightarrow> (\<box>(\<diamond>\<phi>))\<rfloor>"  by simp

text \<open>Axioms of E holds\<close>

lemma Abs: "\<lfloor>\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> \<box>\<circle><\<psi>|\<phi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by blast 
lemma Nec: "\<lfloor>\<box>\<psi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by blast 
lemma Ext: "\<lfloor>\<box>(\<phi>\<^sub>1\<^bold>\<leftrightarrow>\<phi>\<^sub>2) \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>\<^sub>1> \<^bold>\<leftrightarrow> \<circle><\<psi>|\<phi>\<^sub>2>)\<rfloor>"  
  \<comment>\<open>sledgehammer\<close>
  by simp
lemma Id: "\<lfloor>\<circle><\<phi>|\<phi>>\<rfloor>"  
  \<comment>\<open>sledgehammer\<close>
  by blast 
lemma Sh: "\<lfloor>\<circle><\<psi>|\<phi>\<^sub>1\<^bold>\<and>\<phi>\<^sub>2> \<^bold>\<rightarrow> \<circle><(\<phi>\<^sub>2\<^bold>\<rightarrow>\<psi>)|\<phi>\<^sub>1>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by blast 
lemma COK:"\<lfloor>\<circle><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circle><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circle><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by blast

text \<open>Max-Limitedness corresponds to D:\<close>

lemma "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>)\<rfloor>" 
  nitpick [card i=3]  \<comment>\<open>counterexample found\<close>
  oops 

lemma "\<lfloor>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"
  nitpick [card i=3]  \<comment>\<open>counterexample found\<close>
  oops 

lemma "\<lfloor>\<circle><\<chi>|(\<phi>\<^bold>\<or>\<psi>)> \<^bold>\<rightarrow> ((\<circle><\<chi>|\<phi>>) \<^bold>\<or> (\<circle><\<chi>|\<psi>>))\<rfloor>"
  nitpick [card i=3]  \<comment>\<open>counterexample found\<close>
  oops 

theorem T8: 
  assumes mlimitedness
  shows  "D*": "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>\<rfloor>"  
  \<comment>\<open>sledgehammer\<close>
  by (metis assms)

lemma 
  assumes "D*": "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<^bold>\<not>\<psi>|\<phi>>)\<rfloor>"
  shows mlimitedness 
  nitpick [card i=3]  \<comment>\<open>counterexample found\<close>
  oops

text \<open>Smoothness corresponds to cautious monotony:\<close>

theorem T9: 
  assumes msmoothness    
  shows CM: "\<lfloor>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  using assms by force 

lemma 
  assumes CM: "\<lfloor>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"
  shows  msmoothness
  nitpick [card i=3]  \<comment>\<open>counterexample found\<close>
  oops  

text \<open>Interval order corresponds to disjunctive rationality:\<close>

lemma 
  assumes reflexivity
  shows  DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  nitpick [card i=3]  \<comment>\<open>counterexample found\<close>
  oops 

theorem T10: 
  assumes reflexivity and Ferrers
  shows  DR: "\<lfloor>\<circle><\<chi>|(\<phi>\<^bold>\<or>\<psi>)> \<^bold>\<rightarrow> (\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by (metis assms(1) assms(2))
  
lemma 
  assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  shows reflexivity 
  nitpick [card i=1]  \<comment>\<open>counterexample found\<close> 
  oops 

lemma 
  assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  shows Ferrers  
  nitpick [card i=2]  \<comment>\<open>counterexample found\<close>
  oops 

text \<open>Transitivity and totalness corresponds to the Spohn axiom (Sp):\<close>

lemma 
  assumes transitivity
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [card i=3] \<comment>\<open>counterexample found\<close> 
  oops

lemma 
  assumes totality
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [card i=3] \<comment>\<open>counterexample found\<close>
  oops

theorem T11: 
  assumes transitivity and totality
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  by (metis assms)

theorem T12: 
  assumes transitivity and totality
  shows  transit: "\<lfloor>( P<\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> P<\<psi>|\<psi>\<^bold>\<or>\<chi>>) \<^bold>\<rightarrow> P<\<phi>|(\<phi>\<^bold>\<or>\<chi>)>\<rfloor>" 
  by (metis assms(1) assms(2))
                                                          
lemma 
  assumes  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  shows totality   
  nitpick [card i=1] \<comment>\<open>counterexample found\<close> 
  oops

lemma 
  assumes  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  shows transitivity 
  nitpick [card i=2] \<comment>\<open>counterexample found\<close> 
  oops 

subsection \<open>Correspondence under the opt rule\<close>

text \<open>opt-limitedness corresponds to D:\<close>

theorem T13: 
  assumes olimitedness   
  shows  D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<odot><\<psi>|\<phi>> \<^bold>\<rightarrow> \<P><\<psi>|\<phi>>\<rfloor>"   
  by (simp add: assms) 

lemma 
  assumes D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<odot><\<psi>|\<phi>> \<^bold>\<rightarrow> \<P><\<psi>|\<phi>>\<rfloor>"         
  shows olimitedness   
  nitpick [card i=1] \<comment>\<open>counterexample found\<close>  
  oops 

text \<open>Smoothness corresponds to cautious monotony:\<close>

theorem T14: 
  assumes osmoothness   
  shows CM': "\<lfloor>( \<odot><\<psi>|\<phi>> \<^bold>\<and> \<odot><\<chi>|\<phi>> ) \<^bold>\<rightarrow> \<odot><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"   
  using assms by force 


lemma 
  assumes CM: "\<lfloor>( \<odot><\<psi>|\<phi>> \<^bold>\<and> \<odot><\<chi>|\<phi>> ) \<^bold>\<rightarrow> \<odot><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  shows  osmoothness 
  nitpick [card i=1] \<comment>\<open>counterexample found\<close>
  oops
 

text \<open>Transitivity:\<close>

theorem T15: 
  assumes transitivity   
  shows  Sp': "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
  by (metis assms) 

theorem T16: 
  assumes transitivity    
  shows  Trans': "\<lfloor>( \<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<psi>|\<psi>\<^bold>\<or>\<xi>> )\<^bold>\<rightarrow> \<P><\<phi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"   
  by (metis assms) 

lemma 
  assumes Sp: "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>> ) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"
  assumes Trans: "\<lfloor>( \<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<psi>|\<psi>\<^bold>\<or>\<xi>> ) \<^bold>\<rightarrow> \<P><\<phi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"
  shows transitivity    
  nitpick [card i=2] \<comment>\<open>counterexample found\<close>
  oops 

text \<open>Interval order corresponds to disjunctive rationality:\<close>

lemma 
  assumes reflexivity
  shows  DR': "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>"   
  nitpick [card i=3] \<comment>\<open>counterexample found\<close>   
  oops 

theorem T17: 
  assumes reflexivity and Ferrers
  shows  DR': "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>"   
  by (metis assms(2))
 
lemma 
  assumes DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>" 
  shows reflexivity   
  nitpick [card i=1] \<comment>\<open>counterexample found\<close>  
  oops 

lemma 
  assumes DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>" 
  shows Ferrers  
  nitpick [card i=2] \<comment>\<open>counterexample found\<close>
  oops 

subsection \<open>Relationship Lewis rule and max/opt rule\<close>

text \<open>Deontic explosion — max rule:\<close>

theorem DEX: "\<lfloor>(\<diamond>\<phi> \<^bold>\<and> \<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<^bold>\<not>\<psi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>>\<rfloor>" 
  by blast  

text \<open>No deontic explosion — lewis rule:\<close>

lemma DEX: "\<lfloor>(\<diamond>\<phi> \<^bold>\<and> \<circ><\<psi>|\<phi>> \<^bold>\<and> \<circ><\<^bold>\<not>\<psi>|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|\<phi>>\<rfloor>"
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops

theorem T18:
  assumes mlimitedness and transitivity and totality
  shows "\<lfloor>\<circ><\<psi>|\<phi>>\<^bold>\<leftrightarrow>\<odot><\<psi>|\<phi>>\<rfloor>"   
  \<comment>\<open>sledgehammer\<close>
  by (smt (z3) assms)

theorem T19: 
  assumes mlimitedness and transitivity and totality
  shows "\<lfloor>\<circ><\<psi>|\<phi>>\<^bold>\<leftrightarrow>\<circle><\<psi>|\<phi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by (smt (z3) assms) 

text \<open>The axioms of E holding irrespective of the properties of the betterness relation.\<close>

theorem Abs': "\<lfloor>\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<box>\<circ><\<psi>|\<phi>>\<rfloor>"   
  \<comment>\<open>sledgehammer\<close> 
  by auto
theorem Nec': "\<lfloor>\<box>\<psi> \<^bold>\<rightarrow> \<circ><\<psi>|\<phi>>\<rfloor>"  
  \<comment>\<open>sledgehammer\<close>
  by auto
theorem Ext': "\<lfloor>\<box>(\<phi>\<^sub>1\<^bold>\<leftrightarrow>\<phi>\<^sub>2) \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>\<^sub>1> \<^bold>\<leftrightarrow> \<circ><\<psi>|\<phi>\<^sub>2>)\<rfloor>"  
  \<comment>\<open>sledgehammer\<close> 
  by auto
theorem Id': "\<lfloor>\<circ><\<phi>|\<phi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  by auto
theorem Sh': "\<lfloor>\<circ><\<psi>|\<phi>\<^sub>1\<^bold>\<and>\<phi>\<^sub>2> \<^bold>\<rightarrow> \<circ><(\<phi>\<^sub>2\<^bold>\<rightarrow>\<psi>)|\<phi>\<^sub>1>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  by auto


subsection \<open>The axioms of E, F, F+CM, G that are invalid in the absence of any properties of the betterness relation\<close>

lemma D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<integral><\<psi>|\<phi>>)\<rfloor>"
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops

lemma Sp: "\<lfloor>( \<integral><\<psi>|\<phi>> \<^bold>\<and> \<circ><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [expect=genuine,card i=3] \<comment>\<open>counterexample found\<close> 
  oops 

lemma COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops 

lemma CM: "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops 


subsection \<open>Correspondence Lewis\<close>


text \<open>The axioms of E hold if r is total.\<close>

theorem T20:
  assumes totality
  shows "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<integral><\<psi>|\<phi>>)\<rfloor>" 
  using assms by blast

text \<open>The axiom or law of G holds if the betterness relation is transitive.\<close>

theorem T21:
  assumes transitivity
  shows Sp'': "\<lfloor>(\<integral><\<psi>|\<phi>> \<^bold>\<and> \<circ><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
 \<comment>\<open>sledgehammer\<close>
  using assms by blast 

theorem T22:
  assumes transitivity
  shows  Tr'': "\<lfloor>(\<integral><\<phi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<and>\<integral><\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> \<integral><\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  using assms by blast

lemma
  assumes Sp'': "\<lfloor>( \<integral><\<psi>|\<phi>> \<^bold>\<and> \<circ><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"  
  shows transitivity
  nitpick  \<comment>\<open>counterexample found\<close> 
  oops

lemma
  assumes  Tr'': "\<lfloor>(\<integral><\<phi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<and>\<integral><\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> \<integral><\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>" 
  shows transitivity
  nitpick  \<comment>\<open>counterexample found\<close> 
  oops

lemma
  assumes transitivity
  shows COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops  

lemma 
  assumes totality
  shows COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [expect=genuine,card i=3] \<comment>\<open>counterexample found\<close> 
  oops 

text \<open>The axioms of G hold if the betterness relation is both transitive and total.\<close>

theorem T23:
  assumes transitivity and totality
  shows COK':"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  by (smt (verit, ccfv_SIG) assms(1) assms(2)) 

theorem T24:
  assumes transitivity and totality
  shows CM'': "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  by (metis assms)

text \<open>Under the opt rule transitivity alone is equivalent to Sp and Trans.\<close>

theorem T25:
  assumes transitivity 
  shows "\<lfloor>(\<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
  by (metis assms) 

lemma 
  assumes "transitivity"    
  shows  "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<xi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<xi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"   
  nitpick [expect=genuine,card i=2]  \<comment>\<open>counterexample found\<close> 
  oops 

lemma 
  assumes Sp: "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"
          and  Trans: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<xi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<xi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"
  shows transitivity    
  nitpick [expect=genuine,card i=2]  \<comment>\<open>counterexample found\<close> 
  oops 

end