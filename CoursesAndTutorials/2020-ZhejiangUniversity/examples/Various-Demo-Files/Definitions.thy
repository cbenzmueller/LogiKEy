theory Definitions imports Main   (* Christoph Benzmüller and Alexander Steen, 2019 *)
begin
  typedecl i (*Type of possible worlds.*)  typedecl  \<mu> (*Type of individuals.*)
  type_synonym \<sigma>="(i\<Rightarrow>bool)" (*Type of world depended formulas (truth sets).*) 
  type_synonym \<alpha>="(i\<Rightarrow>i\<Rightarrow>bool)" (*Type of accessibility relations between worlds.*)

 (*Modal logic connectives encoded in higher-order logic, including quantifiers*)
  abbreviation mneg :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
  abbreviation mand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
  abbreviation mor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
  abbreviation mimp :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
  abbreviation mequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"
  abbreviation mallmu :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. \<Phi>(x)(w)"
  abbreviation mallmuB:: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"   
  abbreviation meximu :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi>(x)(w)"
  abbreviation meximuB:: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
  abbreviation mallsi :: "(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>\<^sup>\<sigma>") where "\<^bold>\<forall>\<^sup>\<sigma>\<Phi> \<equiv> \<lambda>w.\<forall>x. \<Phi>(x)(w)"
  abbreviation mallsiB:: "(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>\<^sup>\<sigma>"[8]9) where "\<^bold>\<forall>\<^sup>\<sigma>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>\<sigma>\<phi>"   
  abbreviation mexisi :: "(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>\<^sup>\<sigma>") where "\<^bold>\<exists>\<^sup>\<sigma>\<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi>(x)(w)"
  abbreviation mexisiB:: "(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>\<^sup>\<sigma>"[8]9) where "\<^bold>\<exists>\<^sup>\<sigma>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>\<sigma>\<phi>"   
  abbreviation mbox :: "\<alpha>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>_ _") where "\<^bold>\<box> r \<phi> \<equiv> (\<lambda>w. \<forall>v. r w v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<alpha>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>_ _") where "\<^bold>\<diamond> r \<phi> \<equiv> (\<lambda>w. \<exists>v. r w v \<and> \<phi> v)" 

 (*Global and local validity of modal logic formulas*)
  abbreviation global_valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]8) where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> w"
  consts cw :: i (*Current world; uninterpreted constant of type i*)
  abbreviation local_valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>c\<^sub>w"[9]10) where "\<lfloor>\<phi>\<rfloor>\<^sub>c\<^sub>w \<equiv> \<phi> cw"
end