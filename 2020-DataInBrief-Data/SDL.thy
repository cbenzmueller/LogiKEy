theory SDL        (* SDL: Standard Deontic Logic. C. Benzmüller & X. Parent, 2019 *)
  imports Main 
begin
 typedecl i (*Type for possible worlds.*)  
 type_synonym \<sigma> = "(i\<Rightarrow>bool)"
 type_synonym \<gamma> = "\<sigma>\<Rightarrow>\<sigma>" 
 type_synonym \<rho> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"

 consts R::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "R" 70) (*Accessibility relation.*)  
        aw::i (*Actual world.*)  

 abbreviation SDLtop::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
 abbreviation SDLbot::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False" 
 abbreviation SDLnot::\<gamma> ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
 abbreviation SDLand::\<rho> (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<and> \<psi>(w)"   
 abbreviation SDLor::\<rho> (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<or> \<psi>(w)"   
 abbreviation SDLimp::\<rho> (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<longrightarrow> \<psi>(w)"  
 abbreviation SDLequ::\<rho> (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<longleftrightarrow> \<psi>(w)"  

 abbreviation SDLobligatory::\<gamma> ("OB") where "OB \<phi> \<equiv> \<lambda>w. \<forall>v.  w R v \<longrightarrow> \<phi>(v)"
 abbreviation SDLpermissible::\<gamma> ("PE") where "PE \<phi> \<equiv> \<^bold>\<not>(OB(\<^bold>\<not>\<phi>))"
 abbreviation SDLimpermissible::\<gamma> ("IM") where "IM \<phi> \<equiv> OB(\<^bold>\<not>\<phi>)"
 abbreviation SDLomissible::\<gamma> ("OM") where "OM \<phi> \<equiv> \<^bold>\<not>(OB \<phi>)"
 abbreviation SDLoptional::\<gamma> ("OP") where "OP \<phi> \<equiv> (\<^bold>\<not>(OB \<phi>) \<^bold>\<and>  \<^bold>\<not>(OB(\<^bold>\<not>\<phi>)))"

 abbreviation SDLvalid::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[7]105)  where "\<lfloor>A\<rfloor> \<equiv> \<forall>w. A w"       (*Global validity.*)
 abbreviation SDLvalidcw::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105)    where "\<lfloor>A\<rfloor>\<^sub>l \<equiv> A aw"   (*Validity in actual world.*)

(*Possibilist Quantification.*)
 abbreviation SDLforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
 abbreviation SDLforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
 abbreviation SDLexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
 abbreviation SDLexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

 axiomatization where D: "\<lfloor>\<^bold>\<not> ((OB \<phi>) \<^bold>\<and> (OB (\<^bold>\<not> \<phi>)))\<rfloor>" (*Axiom D: seriality of r.*)
 lemma seriality: "(\<forall>w. \<exists>v. w R v)" using D by blast

 abbreviation SDLobl::\<gamma> ("\<^bold>\<circle><_>") where "\<^bold>\<circle><\<phi>> \<equiv>  OB \<phi>"  (*New syntax: A is obligatory.*)

(*Consistency confirmed by model finder Nitpick.*) 
 lemma True nitpick[satisfy,user_axioms,expect=genuine] oops 
 
(*Barcan formulas.*) 
 lemma Barcan:         "\<lfloor>(\<^bold>\<forall>d. \<^bold>\<circle><\<phi>(d)>) \<^bold>\<rightarrow> (\<^bold>\<circle><\<^bold>\<forall>d. \<phi>(d)>)\<rfloor>" by simp  
 lemma ConverseBarcan: "\<lfloor>(\<^bold>\<circle><\<^bold>\<forall>d. \<phi>(d)>) \<^bold>\<rightarrow> (\<^bold>\<forall>d. \<^bold>\<circle><\<phi>(d)>)\<rfloor>" by simp 
end







