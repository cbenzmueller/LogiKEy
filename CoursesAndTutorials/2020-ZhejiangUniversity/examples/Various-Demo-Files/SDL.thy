theory SDL imports Main                   (* Christoph Benzmüller & Xavier Parent, 2018 *)

begin  (* SDL: Standard Deontic Logic (Modal Logic D) *)
 typedecl i (*type for possible worlds*)  type_synonym \<sigma> = "(i\<Rightarrow>bool)"
 consts r::"i\<Rightarrow>i\<Rightarrow>bool" (infixr"r"70) (*Accessibility relation.*)  cw::i (*Current world.*)  

 abbreviation mtop ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
 abbreviation mbot ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False" 
 abbreviation mnot ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
 abbreviation mand (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
 abbreviation mor  (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
 abbreviation mimp (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
 abbreviation mequ (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"  
 abbreviation mobligatory ("OB") where "OB \<phi> \<equiv> \<lambda>w. \<forall>v. w r v \<longrightarrow> \<phi>(v)" (*obligatory*)
 abbreviation mpermissible ("PE") where "PE \<phi> \<equiv> \<^bold>\<not>(OB(\<^bold>\<not>\<phi>))" (*permissible*)
 abbreviation mimpermissible ("IM") where "IM \<phi> \<equiv> OB(\<^bold>\<not>\<phi>)"  (*impermissible*)
 abbreviation omissible ("OM") where "OM \<phi> \<equiv> \<^bold>\<not>(OB \<phi>)" (*omissible*)
 abbreviation moptional ("OP") where "OP \<phi> \<equiv> (\<^bold>\<not>(OB \<phi>) \<^bold>\<and>  \<^bold>\<not>(OB(\<^bold>\<not>\<phi>)))" (*optional*)
 
 abbreviation ddlvalid::"\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]105)      (*Global Validity*)
  where "\<lfloor>A\<rfloor> \<equiv> \<forall>w. A w"  
 abbreviation ddlvalidcw::"\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>c\<^sub>w"[7]105)  (*Local Validity (in cw)*)
  where "\<lfloor>A\<rfloor>\<^sub>c\<^sub>w \<equiv> A cw" 

(* The D axiom is postulated *)
 axiomatization where D: "\<lfloor>\<^bold>\<not> ((OB \<phi>) \<^bold>\<and> (OB (\<^bold>\<not> \<phi>)))\<rfloor>"    

(* Meta-level study: D corresponds to seriality *)
 lemma "\<lfloor>\<^bold>\<not> ((OB \<phi>) \<^bold>\<and> (OB (\<^bold>\<not> \<phi>)))\<rfloor> \<longleftrightarrow> (\<forall>w. \<exists>v. w r v)" by auto

 lemma "\<lfloor>(OB \<phi>) \<^bold>\<rightarrow> (\<^bold>\<not> (OB (\<^bold>\<not> \<phi>)))\<rfloor>" using D by blast

 lemma assumes "\<lfloor>(OB \<phi>) \<^bold>\<rightarrow> (\<^bold>\<not> (OB (\<^bold>\<not> \<phi>)))\<rfloor>" shows  "\<lfloor>\<^bold>\<not> ((OB \<phi>) \<^bold>\<and> (OB (\<^bold>\<not> \<phi>)))\<rfloor>" using assms by blast


(* Standardised syntax: unary operator for obligation in SDL *)
abbreviation obligatorySDL::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>O\<^bold>\<langle>_\<^bold>\<rangle>") where "\<^bold>O\<^bold>\<langle>A\<^bold>\<rangle>  \<equiv>  OB A" 
abbreviation obligatorySDL'::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circle><_>") where "\<^bold>\<circle><A>  \<equiv>  OB A" 

(* Consistency *)
  lemma True nitpick [satisfy] oops  

 (* Unimportant *)
  sledgehammer_params [max_facts=20,timeout=20] (* Sets parameters for theorem provers *)
  nitpick_params [user_axioms,expect=genuine,show_all,format=2] (* ... and model finder. *)

end

