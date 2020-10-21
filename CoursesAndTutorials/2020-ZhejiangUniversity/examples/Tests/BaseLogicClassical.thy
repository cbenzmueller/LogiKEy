theory BaseLogicClassical imports Main                      
begin      
(*Type declarations and type abbreviations*)
type_synonym \<sigma> = "bool" (*Propositions*)
type_synonym \<mu> = "\<sigma>\<Rightarrow>\<sigma>" (*Unary modal connectives*)
type_synonym \<nu> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (*Binary modal connectives*)

(*Classical logic connectives*)
abbreviation ClFalse::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> False"
abbreviation ClTrue::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> True"
abbreviation ClNeg::\<mu> ("\<^bold>\<not>_") where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"
abbreviation ClAnd::\<nu> ("_\<^bold>\<and>_") where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<phi> \<and> \<psi>"   
abbreviation ClOr::\<nu> ("_\<^bold>\<or>_") where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<phi> \<or> \<psi>"
abbreviation ClImp::\<nu> ("_\<^bold>\<rightarrow>_") where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"  
abbreviation ClEquiv::\<nu> ("_\<^bold>\<leftrightarrow>_") where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<phi> \<longleftrightarrow> \<psi>"



consts ClBox::"'a\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>[_\<^bold>] _") 
consts ClDia::"'a\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold><_\<^bold>> _") 


(*Possibilist quantification for type bool*)
abbreviation ClAll ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x.(\<Phi> x)"
abbreviation ClAllB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation ClEx ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<exists>x.(\<Phi> x)"   
abbreviation CLExB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 


(*Meta-logical predicate for global validity*)
abbreviation g1::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<psi>"
(*Meta-logical predicate for local validity*)
abbreviation MlValid::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>c\<^sub>w") where "\<lfloor>\<psi>\<rfloor>\<^sub>c\<^sub>w \<equiv>  \<psi>"

(*Consistency, Barcan and converse Barcan formula*)
lemma True nitpick[satisfy] oops  (*Model found by Nitpick*)
lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>[r\<^bold>](\<phi> x)) \<^bold>\<rightarrow> \<^bold>[r\<^bold>](\<^bold>\<forall>x. \<phi> x)\<rfloor>" sledgehammer nitpick oops
lemma "\<lfloor>(\<^bold>[r\<^bold>](\<^bold>\<forall>x.(\<phi> x))) \<^bold>\<rightarrow> \<^bold>\<forall>x.\<^bold>[r\<^bold>](\<phi> x)\<rfloor>"  sledgehammer nitpick oops (*Ctm*)


(*unimportant*) nitpick_params[user_axioms,show_all]
(*unimportant*) declare [[smt_solver=cvc4,smt_oracle]]
end
