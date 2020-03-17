 
(*X. Parent, 25/08/2019, and C. Benzmüller, 2020 *)
(*This file introduces David Lewis DDL and studies its
relationship with the Aqvist-Hansson DDL  *)
(*This uses material from a chapter for the second volume of the
handbook of deontic logic  *)

theory Lewis_DDL  imports Main  
begin       
typedecl i \<comment>\<open>type for possible worlds\<close>  
type_synonym \<tau> = "(i\<Rightarrow>bool)" 
consts  aw::i \<comment>\<open>actual world\<close>  
 
abbreviation(input) mtrue  :: "\<tau>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
abbreviation(input) mfalse :: "\<tau>" ("\<^bold>\<bottom>")  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"   
abbreviation(input) mnot   :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
abbreviation(input) mand   :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
abbreviation(input) mor    :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
abbreviation(input) mimp   :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
abbreviation(input) mequ   :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"  

abbreviation(input) mbox :: "\<tau>\<Rightarrow>\<tau>" ("\<box>") where "\<box>\<phi> \<equiv> \<lambda>w.  \<forall>v. \<phi>(v)" 
definition ddediomond  :: "\<tau>\<Rightarrow>\<tau>" ("\<diamond>") where "\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. \<phi>(v)"



consts r :: "i\<Rightarrow>\<tau>"  (infixr "r" 70)
 \<comment>\<open>the betterness relation r, used in definition of \<circle><_|_>  \<close>  
abbreviation(input) mopt  :: "\<tau>\<Rightarrow>\<tau>" ("opt<_>") 
  where "opt<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x)  \<longrightarrow>  v r x) )) )" 
abbreviation(input) msubset :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>bool" (infix "\<^bold>\<subseteq>" 53)
  where "\<phi> \<^bold>\<subseteq> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"

(*David Lewis's evaluation rule for the conditional *)
abbreviation(input) mcond  :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<circle><_|_>")
  where "\<circle><\<psi>|\<phi>> \<equiv> (\<lambda>v. (\<not>(\<exists>x. (\<phi>)(x))\<or>  (\<exists>x. ((\<phi>)(x)\<and>(\<psi>)(x) \<and> (\<forall>y. ((y r x) \<longrightarrow> (\<phi>)(y)\<longrightarrow>(\<psi>)(y)))))))"
definition ddeperm :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("P<_|_>") 
  where "P<\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circle><\<^bold>\<not>\<psi>|\<phi>>"

(*Hansson-Aqvist's evaluation rule for the conditional *)
abbreviation(input) mcond2  :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<circle>o<_|_>")
  where "\<circle>o<\<psi>|\<phi>> \<equiv> (\<lambda>v. opt<\<phi>> \<^bold>\<subseteq> \<psi>)"


abbreviation limitedness  where "limitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x))"
abbreviation transitivity where "transitivity \<equiv> (\<forall>x y z. (x r y \<and> y r z) \<longrightarrow> x r z)"
abbreviation totalness where "totalness \<equiv> (\<forall>x y. (x r y \<or> y r x))"
abbreviation reflexivity where "reflexivity \<equiv> (\<forall>x. (x r x))"

abbreviation(input) valid :: "\<tau>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
definition cjactual :: "\<tau>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) 
  where "\<lfloor>p\<rfloor>\<^sub>l \<equiv> p(aw)"
     
lemma True nitpick [satisfy, user_axioms, show_all, expect=genuine] oops     

(*relation with optimality*)
(*The lewis rule is stronger*)

lemma "\<lfloor>\<circle>o<\<psi>|\<phi>>\<^bold>\<rightarrow>\<circle><\<psi>|\<phi>>\<rfloor>"
  nitpick oops

lemma "\<lfloor>\<circle><\<psi>|\<phi>>\<^bold>\<rightarrow>\<circle>o<\<psi>|\<phi>>\<rfloor>"
  sledgehammer oops

lemma
assumes "limitedness"
  assumes "transitivity" 
  shows "\<lfloor>\<circle>o<\<psi>|\<phi>>\<^bold>\<rightarrow>\<circle><\<psi>|\<phi>>\<rfloor>"
   sledgehammer
  by (smt assms(1) assms(2))

(*axioms of E holding irrespective of the properties of r*)

lemma Abs:"\<lfloor>\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> \<box>\<circle><\<psi>|\<phi>>\<rfloor>"  sledgehammer oops
  

lemma Nec:"\<lfloor>\<box>\<psi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>>\<rfloor>" by blast 
  

lemma Ext:"\<lfloor>\<box>(\<phi>\<^sub>1\<^bold>\<leftrightarrow>\<phi>\<^sub>2) \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>\<^sub>1> \<^bold>\<leftrightarrow> \<circle><\<psi>|\<phi>\<^sub>2>)\<rfloor>" by simp 
 

lemma Id:"\<lfloor>\<circle><\<phi>|\<phi>>\<rfloor>" by auto 

lemma Sh:"\<lfloor>\<circle><\<psi>|\<phi>\<^sub>1\<^bold>\<and>\<phi>\<^sub>2> \<^bold>\<rightarrow> \<circle><(\<phi>\<^sub>2\<^bold>\<rightarrow>\<psi>)|\<phi>\<^sub>1>\<rfloor>" by blast
  

lemma MP:"(\<lfloor>\<phi>\<rfloor>\<and>\<lfloor>\<phi>\<^bold>\<rightarrow>\<psi>\<rfloor>)\<Longrightarrow>\<lfloor>\<psi>\<rfloor>" by blast

lemma N:"\<lfloor>\<phi>\<rfloor>\<Longrightarrow>\<lfloor>\<box>\<phi>\<rfloor>" by auto 

 
(*axioms of E holding if r transitive and totale*)

lemma COK:"\<lfloor>\<circle><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circle><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circle><\<psi>\<^sub>2|\<phi>>)\<rfloor>" nitpick oops (*countermodel*)

lemma 
  assumes "transitivity" 
  shows COK:"\<lfloor>\<circle><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circle><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circle><\<psi>\<^sub>2|\<phi>>)\<rfloor>" nitpick oops  (*countermodel*) 

  lemma 
  assumes "totalness"
  shows COK:"\<lfloor>\<circle><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circle><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circle><\<psi>\<^sub>2|\<phi>>)\<rfloor>" nitpick oops (*countermodel*)
  
lemma 
  assumes "transitivity" 
  assumes "totalness"
  shows COK:"\<lfloor>\<circle><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circle><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circle><\<psi>\<^sub>2|\<phi>>)\<rfloor>" by (smt assms(1) assms(2))
  
lemma D : "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>)\<rfloor>"  nitpick oops (*countermodel*)

lemma
 assumes "totalness"
  shows D : "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>)\<rfloor>"  by (smt assms ddediomond_def ddeperm_def) 

lemma  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" nitpick oops (*countermodel*)

lemma
 assumes "transitivity"
 shows Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" by (smt assms ddeperm_def) 

lemma CM: "\<lfloor>(\<circle><\<psi>|\<phi>>\<^bold>\<and>\<circle><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" nitpick oops (*countermodel*)

lemma
  assumes "transitivity"
  shows CM: "\<lfloor>(\<circle><\<psi>|\<phi>>\<^bold>\<and>\<circle><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" nitpick oops (*countermodel*)

lemma
  assumes "transitivity"
  assumes "totalness"
  shows CM: "\<lfloor>(\<circle><\<psi>|\<phi>>\<^bold>\<and>\<circle><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" by (metis assms(1) assms(2)) 

lemma SA:"\<lfloor>\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow>  \<circle><\<psi>|\<phi>\<^bold>\<and>\<chi>>\<rfloor>" nitpick oops (*countermodel*)

end
