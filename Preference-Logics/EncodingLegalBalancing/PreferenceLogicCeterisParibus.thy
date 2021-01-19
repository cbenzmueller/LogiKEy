theory PreferenceLogicCeterisParibus (** Benzmüller & Fuenmayor, 2020 **)
  imports PreferenceLogicBasics
begin (** Ceteris Paribus reasoning by van Benthem et al, JPL 2009 **)
(*Section 5: Equality-based Ceteris Paribus Preference Logic*)
abbreviation a1::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>bool" ("_\<^bold>\<in>_") where "\<phi> \<^bold>\<in> \<Gamma> \<equiv> \<Gamma> \<phi>" 
abbreviation a2 ("_\<^bold>\<subseteq>_") where "\<Gamma> \<^bold>\<subseteq> \<Gamma>' \<equiv> \<forall>\<phi>. \<phi> \<^bold>\<in> \<Gamma> \<longrightarrow> \<phi> \<^bold>\<in> \<Gamma>'" 
abbreviation a3 ("_\<^bold>\<union>_") where "\<Gamma> \<^bold>\<union> \<Gamma>' \<equiv> \<lambda>\<phi>. \<phi> \<^bold>\<in> \<Gamma> \<or> \<phi> \<^bold>\<in> \<Gamma>'" 
abbreviation a4 ("_\<^bold>\<inter>_") where "\<Gamma> \<^bold>\<inter> \<Gamma>' \<equiv> \<lambda>\<phi>. \<phi> \<^bold>\<in> \<Gamma> \<and> \<phi> \<^bold>\<in> \<Gamma>'" 
abbreviation a5 ("\<^bold>{_\<^bold>}") where "\<^bold>{\<phi>\<^bold>} \<equiv> \<lambda>x::\<sigma>. x=\<phi>" 
abbreviation a6 ("\<^bold>{_,_\<^bold>}")   where "\<^bold>{\<alpha>,\<beta>\<^bold>} \<equiv> \<lambda>x::\<sigma>. x=\<alpha> \<or> x=\<beta>" 
abbreviation a7 ("\<^bold>{_,_,_\<^bold>}") where "\<^bold>{\<alpha>,\<beta>,\<gamma>\<^bold>} \<equiv> \<lambda>x::\<sigma>. x=\<alpha> \<or> x=\<beta> \<or> x=\<gamma>" 
abbreviation a8 ("\<^bold>\<emptyset>")   where "\<^bold>\<emptyset> \<equiv> (\<lambda>\<psi>::\<sigma>. False)"
abbreviation a9 ("\<^bold>\<U>")   where "\<^bold>\<U> \<equiv> (\<lambda>\<psi>::\<sigma>. True)"
abbreviation c14 ("_\<^bold>\<equiv>\<^sub>__") where "w \<^bold>\<equiv>\<^sub>\<Gamma> v \<equiv> \<forall>\<phi>. \<phi> \<^bold>\<in> \<Gamma> \<longrightarrow> (\<phi> w \<longleftrightarrow> \<phi> v)"
abbreviation c15 ("_\<^bold>\<unlhd>\<^sub>__") where "w \<^bold>\<unlhd>\<^sub>\<Gamma> v \<equiv> w \<preceq> v \<and> w \<^bold>\<equiv>\<^sub>\<Gamma> v"
abbreviation c16 ("_\<^bold>\<lhd>\<^sub>__") where "w \<^bold>\<lhd>\<^sub>\<Gamma> v \<equiv> w \<prec> v \<and> w \<^bold>\<equiv>\<^sub>\<Gamma> v"
abbreviation c17 ("\<^bold>\<langle>_\<^bold>\<rangle>\<^sup>\<preceq>_") where "\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<exists>v. w \<^bold>\<unlhd>\<^sub>\<Gamma> v \<and> \<phi> v"
abbreviation c18 ("[_]\<^sup>\<preceq>_") where "[\<Gamma>]\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<forall>v. w \<^bold>\<unlhd>\<^sub>\<Gamma> v \<longrightarrow> \<phi> v"
abbreviation c19 ("\<^bold>\<langle>_\<^bold>\<rangle>\<^sup>\<prec>_") where "\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<exists>v. w \<^bold>\<lhd>\<^sub>\<Gamma> v \<and> \<phi> v"
abbreviation c20 ("[_]\<^sup>\<prec>_") where "[\<Gamma>]\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<forall>v. w \<^bold>\<lhd>\<^sub>\<Gamma> v \<longrightarrow> \<phi> v"
abbreviation c21 ("\<^bold>\<langle>_\<^bold>\<rangle>_")  where "\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi> \<equiv> \<lambda>w.\<exists>v. w \<^bold>\<equiv>\<^sub>\<Gamma> v \<and> \<phi> v"
abbreviation c22 ("[_]_")  where "[\<Gamma>]\<phi> \<equiv> \<lambda>w.\<forall>v. w \<^bold>\<equiv>\<^sub>\<Gamma> v \<longrightarrow> \<phi> v"
(*Section 6: Ceteris Paribus Counterparts of Binary Pref. Statements*)
(*operators below not defined in paper; existence is tacitly suggested.
  AA-variant draws upon von Wright's. AE-variant draws upon Halpern's.*)
abbreviation C23 ("_\<prec>\<^sub>A\<^sub>A\<^sup>__") where "(\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s.\<forall>t. \<phi> s \<and> \<psi> t \<longrightarrow> s \<^bold>\<lhd>\<^sub>\<Gamma> t"
abbreviation c24 ("_\<preceq>\<^sub>A\<^sub>A\<^sup>__") where "(\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s.\<forall>t. \<phi> s \<and> \<psi> t \<longrightarrow> s \<^bold>\<unlhd>\<^sub>\<Gamma> t" 
abbreviation c25 ("_\<prec>\<^sub>A\<^sub>E\<^sup>__") where "(\<phi> \<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s.\<exists>t. \<phi> s \<longrightarrow> \<psi> t \<and> s \<^bold>\<lhd>\<^sub>\<Gamma> t" 
abbreviation c26 ("_\<preceq>\<^sub>A\<^sub>E\<^sup>__") where "(\<phi> \<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s.\<exists>t. \<phi> s \<longrightarrow> \<psi> t \<and> s \<^bold>\<unlhd>\<^sub>\<Gamma> t" 
abbreviation c27 ("_\<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>__") where "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<psi> \<^bold>\<rightarrow> [\<Gamma>]\<^sup>\<preceq>\<^bold>\<not>\<phi>)"
abbreviation c28 ("_\<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>__") where "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<psi> \<^bold>\<rightarrow> [\<Gamma>]\<^sup>\<prec>\<^bold>\<not>\<phi>)"
abbreviation c29 ("_\<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>__") where "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<psi>)" 
abbreviation c30 ("_\<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>__") where "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<psi>)"
(*Consistency confirmed (trivial: only abbreviations are introduced*)
lemma True nitpick[satisfy,user_axioms] oops
end
(*Note: \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> aims at (approximately) modelling von Wright's notion of
ceteris paribus -"all other things being equal"-preferences wrt. a set of
formulas \<Gamma> (which are to be elicited by extra-logical means). These can thus
be better understood as "these (given) things being equal"-preferences.*)
