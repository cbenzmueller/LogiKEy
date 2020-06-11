theory HOML imports Main                      
begin      
(*Type declarations and type abbreviations*)
typedecl i (*Possible worlds*)  
typedecl e (*Individuals*)      
type_synonym \<sigma> = "i\<Rightarrow>bool" (*World-lifted propositions*)
type_synonym \<gamma> = "e\<Rightarrow>\<sigma>" (*Lifted predicates*)
type_synonym \<mu> = "\<sigma>\<Rightarrow>\<sigma>" (*Unary modal connectives*)
type_synonym \<nu> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (*Binary modal connectives*)

(*Modal logic connectives (operating on truth-sets)*)
abbreviation c1::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation c2::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation c3::\<mu> ("\<^bold>\<not>_") where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w.\<not>(\<phi> w)"
abbreviation c4::\<nu> ("_\<^bold>\<and>_") where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<and>(\<psi> w)"   
abbreviation c5::\<nu> ("_\<^bold>\<or>_") where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<or>(\<psi> w)"
abbreviation c6::\<nu> ("_\<^bold>\<rightarrow>_") where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longrightarrow>(\<psi> w)"  
abbreviation c7::\<nu> ("_\<^bold>\<leftrightarrow>_") where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longleftrightarrow>(\<psi> w)"
consts R::"i\<Rightarrow>i\<Rightarrow>bool" ("_\<^bold>r_")  (*Accessibility relation*)
abbreviation c8::\<mu> ("\<^bold>\<box>_") where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v.(w\<^bold>rv)\<longrightarrow>(\<phi> v)"
abbreviation c9::\<mu> ("\<^bold>\<diamond>_") where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v.(w\<^bold>rv)\<and>(\<phi> v)"
abbreviation c10::"\<gamma>\<Rightarrow>\<gamma>" ("\<^bold>\<rightharpoondown>_") 
                           where "\<^bold>\<rightharpoondown>\<Phi> \<equiv> \<lambda>x.\<lambda>w.\<not>(\<Phi> x w)"
abbreviation c11::"e\<Rightarrow>e\<Rightarrow>\<sigma>" ("_\<^bold>=_") where "x\<^bold>=y \<equiv> \<lambda>w.(x=y)"
abbreviation c12::"e\<Rightarrow>e\<Rightarrow>\<sigma>" ("_\<^bold>\<noteq>_") where "x\<^bold>\<noteq>y \<equiv> \<lambda>w.(x\<noteq>y)"

(*Polymorphic possibilist quantification*)
abbreviation q1::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") 
                                where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x.(\<Phi> x w)"
abbreviation q2 (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation q3::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") 
                                where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x.(\<Phi> x w)"   
abbreviation q4 (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

(*Actualist quantification for individuals*)
consts existsAt::\<gamma> ("_\<^bold>@_")  
abbreviation q5::"\<gamma>\<Rightarrow>\<sigma>" ("\<^bold>\<forall>\<^sup>E") 
             where "\<^bold>\<forall>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<forall>x.(x\<^bold>@w)\<longrightarrow>(\<Phi> x w)"
abbreviation q6 (binder"\<^bold>\<forall>\<^sup>E"[8]9) where "\<^bold>\<forall>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E\<phi>"     
abbreviation q7::"\<gamma>\<Rightarrow>\<sigma>" ("\<^bold>\<exists>\<^sup>E") 
             where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<exists>x.(x\<^bold>@w)\<and>(\<Phi> x w)"
abbreviation q8 (binder"\<^bold>\<exists>\<^sup>E"[8]9) where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"

(*Meta-logical predicate for global validity*)
abbreviation g1::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w. \<psi> w"

(*Consistency, Barcan and converse Barcan formula*)
lemma True nitpick[satisfy] oops  (*Model found by Nitpick*)
lemma "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x))\<rfloor>" nitpick oops (*Ctm*)
lemma "\<lfloor>(\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x))) \<^bold>\<rightarrow> \<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x)\<rfloor>" nitpick oops (*Ctm*)
lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. \<phi> x)\<rfloor>" by simp 
lemma "\<lfloor>(\<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x))) \<^bold>\<rightarrow> \<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)\<rfloor>" by simp

(*unimportant*) nitpick_params[user_axioms,show_all]
(*unimportant*) declare [[smt_solver=cvc4,smt_oracle]]
end


