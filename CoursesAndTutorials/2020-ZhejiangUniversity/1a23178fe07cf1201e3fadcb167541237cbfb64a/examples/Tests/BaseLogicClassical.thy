theory BaseLogicClassical imports Main                      
begin      
(*Type declarations and type abbreviations*)
typedecl i (*Possible worlds*)  
typedecl e (*Individuals*)      
type_synonym \<sigma> = "bool" (*World-lifted propositions*)
type_synonym \<tau> = "i\<Rightarrow>i\<Rightarrow>bool" (*Lifted predicates*)
type_synonym \<gamma> = "e\<Rightarrow>\<sigma>" (*Lifted predicates*)
type_synonym \<mu> = "\<sigma>\<Rightarrow>\<sigma>" (*Unary modal connectives*)
type_synonym \<nu> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (*Binary modal connectives*)

(*Modal logic connectives (operating on truth-sets)*)
abbreviation c1::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> False"
abbreviation c2::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> True"
abbreviation c3::\<mu> ("\<^bold>\<not>_") where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"
abbreviation c4::\<nu> ("_\<^bold>\<and>_") where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<phi> \<and> \<psi>"   
abbreviation c5::\<nu> ("_\<^bold>\<or>_") where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<phi> \<or> \<psi>"
abbreviation c6::\<nu> ("_\<^bold>\<rightarrow>_") where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"  
abbreviation c7::\<nu> ("_\<^bold>\<leftrightarrow>_") where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<phi> \<longleftrightarrow> \<psi>"

(*
consts KidOfAccessRel::"\<tau>\<Rightarrow>e" Box::"e\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" Dia::"e\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
abbreviation c8::"\<tau>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>[_\<^bold>] _") where "\<^bold>[r\<^bold>] \<phi> \<equiv> (Box  (KidOfAccessRel r) \<phi>)"
abbreviation c9::"\<tau>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold><_\<^bold>> _") where "\<^bold><r\<^bold>> \<phi> \<equiv> (Dia (KidOfAccessRel r) \<phi>)"
*)

consts c8::"\<tau>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>[_\<^bold>] _") 
consts c9::"\<tau>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold><_\<^bold>> _") 


(*Polymorphic possibilist quantification*)
abbreviation q1::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") 
                                where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x.(\<Phi> x)"
abbreviation q2 (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation q3::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") 
                                where "\<^bold>\<exists>\<Phi> \<equiv> \<exists>x.(\<Phi> x)"   
abbreviation q4 (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

(*Actualist quantification for individuals*)
consts existsAt::\<gamma> 
abbreviation q5::"\<gamma>\<Rightarrow>\<sigma>" ("\<^bold>\<forall>\<^sup>E") 
             where "\<^bold>\<forall>\<^sup>E\<Phi> \<equiv> \<forall>x.(existsAt x)\<longrightarrow>(\<Phi> x)"
abbreviation q6 (binder"\<^bold>\<forall>\<^sup>E"[8]9) where "\<^bold>\<forall>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E\<phi>"     
abbreviation q7::"\<gamma>\<Rightarrow>\<sigma>" ("\<^bold>\<exists>\<^sup>E") 
             where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<exists>x.(existsAt x)\<and>(\<Phi> x)"
abbreviation q8 (binder"\<^bold>\<exists>\<^sup>E"[8]9) where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"

(*Meta-logical predicate for global validity*)
abbreviation g1::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<psi>"

(*
(*Consistency, Barcan and converse Barcan formula*)
lemma True nitpick[satisfy] oops  (*Model found by Nitpick*)
lemma "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.\<^bold>[r\<^bold>](\<phi> x)) \<^bold>\<rightarrow> \<^bold>[r\<^bold>](\<^bold>\<forall>\<^sup>Ex.(\<phi> x))\<rfloor>" nitpick oops (*Ctm*)
lemma "\<lfloor>(\<^bold>[r\<^bold>](\<^bold>\<forall>\<^sup>Ex.(\<phi> x))) \<^bold>\<rightarrow> \<^bold>\<forall>\<^sup>Ex.\<^bold>[r\<^bold>](\<phi> x)\<rfloor>" nitpick oops (*Ctm*)
lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>[r\<^bold>](\<phi> x)) \<^bold>\<rightarrow> \<^bold>[r\<^bold>](\<^bold>\<forall>x. \<phi> x)\<rfloor>" by smt oops 
lemma "\<lfloor>(\<^bold>[r\<^bold>](\<^bold>\<forall>x.(\<phi> x))) \<^bold>\<rightarrow> \<^bold>\<forall>x.\<^bold>[r\<^bold>](\<phi> x)\<rfloor>" nitpick[show_all,format=2] oops (*Ctm*)
*)

(*unimportant*) nitpick_params[user_axioms,show_all]
(*unimportant*) declare [[smt_solver=cvc4,smt_oracle]]
end
