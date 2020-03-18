theory HOMML imports Main                            (* By Christoph Benzmüller, 2018 *)
 
begin (*An Embedding of Higher-Order Multi-Modal Logic (HOMML) in HOL.*)

  typedecl i (*Type of possible worlds.*) typedecl \<mu> (*Type of individuals.*)
  type_synonym \<sigma>="(i\<Rightarrow>bool)" (*Type of world depended formulas (truth sets).*) 
  type_synonym \<alpha>="(i\<Rightarrow>i\<Rightarrow>bool)" (*Type of accessibility relations between worlds.*)

 (*Lifted HOMML connectives: they operate on world depended formulas (truth sets).*)
  definition mtop :: "\<sigma>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
  definition mbot :: "\<sigma>" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False" 
  definition mneg :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
  definition mand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
  definition mor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
  definition mimp :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
  definition mequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"
  definition mall :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. \<Phi>(x)(w)"
  definition mallB:: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"   
  definition mexi :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi>(x)(w)"
  definition mexiB:: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
  definition mbox :: "\<alpha>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>_ _") where "\<^bold>\<box> r \<phi> \<equiv> (\<lambda>w. \<forall>v. r w v \<longrightarrow> \<phi> v)"
  definition mdia :: "\<alpha>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>_ _") where "\<^bold>\<diamond> r \<phi> \<equiv> (\<lambda>w. \<exists>v. r w v \<and> \<phi> v)" 

 (*Global and local validity of lifted formulas*)
  definition global_valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]8) where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> w"
  consts cw :: i (*Current world; uninterpreted constant of type i*)
  definition local_valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>c\<^sub>w"[9]10) where "\<lfloor>\<phi>\<rfloor>\<^sub>c\<^sub>w \<equiv> \<phi> cw"

 (*Introducing "Defs" as the set of the above definitions; useful for convenient unfolding.*)
 named_theorems Defs declare mtop_def[Defs] mbot_def[Defs] mneg_def[Defs] mand_def[Defs] 
  mor_def[Defs] mimp_def[Defs] mequ_def[Defs] mall_def[Defs] mallB_def[Defs] mexi_def[Defs] 
  mexiB_def[Defs] mbox_def[Defs] mdia_def[Defs] global_valid_def[Defs] local_valid_def[Defs]
end 
