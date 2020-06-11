theory PreferenceLogicCeterisParibus         (*** Benzmüller & Fuenmayor, 2020 ***)
  imports PreferenceLogicBasics
begin (* Ceteris Paribus reasoning for preference logic 
         by van Benthem, Girard and Roy, JPL 2009, in HOL*)

(**** Section 5: Equality-based Ceteris Paribus Preference Logic ****)
abbreviation elem::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>bool" ("_\<^bold>\<in>_") where "\<phi> \<^bold>\<in> \<Gamma> \<equiv> \<Gamma> \<phi>" 
abbreviation subs::"\<pi>\<Rightarrow>\<pi>\<Rightarrow>bool" ("_\<^bold>\<subseteq>_") where "\<Gamma> \<^bold>\<subseteq> \<Gamma>' \<equiv> \<forall>\<phi>. \<phi> \<^bold>\<in> \<Gamma> \<longrightarrow> \<phi> \<^bold>\<in> \<Gamma>'" 
abbreviation union::"\<pi>\<Rightarrow>\<pi>\<Rightarrow>\<pi>"   ("_\<^bold>\<union>_") where "\<Gamma> \<^bold>\<union> \<Gamma>' \<equiv> \<lambda>\<phi>. \<phi> \<^bold>\<in> \<Gamma> \<or> \<phi> \<^bold>\<in> \<Gamma>'" 
abbreviation intsec::"\<pi>\<Rightarrow>\<pi>\<Rightarrow>\<pi>"  ("_\<^bold>\<inter>_") where "\<Gamma> \<^bold>\<inter> \<Gamma>' \<equiv> \<lambda>\<phi>. \<phi> \<^bold>\<in> \<Gamma> \<and> \<phi> \<^bold>\<in> \<Gamma>'" 
abbreviation mkSet1::"\<sigma>\<Rightarrow>\<pi>"     ("\<^bold>{_\<^bold>}") where "\<^bold>{\<phi>\<^bold>} \<equiv> \<lambda>x. x=\<phi>" 
abbreviation mkSet2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<pi>"  ("\<^bold>{_,_\<^bold>}")     where "\<^bold>{\<alpha>,\<beta>\<^bold>} \<equiv> \<lambda>x. x=\<alpha> \<or> x=\<beta>" 
abbreviation mkSet3::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<pi>" ("\<^bold>{_,_,_\<^bold>}") where "\<^bold>{\<alpha>,\<beta>,\<gamma>\<^bold>} \<equiv> \<lambda>x. x=\<alpha> \<or> x=\<beta> \<or> x=\<gamma>" 
abbreviation emptyS::"\<sigma>\<Rightarrow>bool"  ("\<^bold>\<emptyset>")   where "\<^bold>\<emptyset> \<equiv> (\<lambda> \<psi>. False)"
abbreviation univS::"\<sigma>\<Rightarrow>bool"   ("\<^bold>\<U>")   where "\<^bold>\<U> \<equiv> (\<lambda> \<psi>. True)"

abbreviation c14::"i\<Rightarrow>\<pi>\<Rightarrow>\<sigma>" ("_\<^bold>\<equiv>\<^sub>__") where "w \<^bold>\<equiv>\<^sub>\<Gamma> v \<equiv> \<forall>\<phi>. \<phi> \<^bold>\<in> \<Gamma> \<longrightarrow> (\<phi> w \<longleftrightarrow> \<phi> v)"
abbreviation c15::"i\<Rightarrow>\<pi>\<Rightarrow>\<sigma>" ("_\<^bold>\<unlhd>\<^sub>__") where "w \<^bold>\<unlhd>\<^sub>\<Gamma> v \<equiv> w \<preceq> v \<and> w \<^bold>\<equiv>\<^sub>\<Gamma> v"
abbreviation c16::"i\<Rightarrow>\<pi>\<Rightarrow>\<sigma>" ("_\<^bold>\<lhd>\<^sub>__") where "w \<^bold>\<lhd>\<^sub>\<Gamma> v \<equiv> w \<prec> v \<and> w \<^bold>\<equiv>\<^sub>\<Gamma> v"
abbreviation c17::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<langle>_\<^bold>\<rangle>\<^sup>\<preceq>_") where "\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<exists>v. w \<^bold>\<unlhd>\<^sub>\<Gamma> v \<and> \<phi> v"
abbreviation c18::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("[_]\<^sup>\<preceq>_") where "[\<Gamma>]\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<forall>v. w \<^bold>\<unlhd>\<^sub>\<Gamma> v \<longrightarrow> \<phi> v"
abbreviation c19::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<langle>_\<^bold>\<rangle>\<^sup>\<prec>_") where "\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<exists>v. w \<^bold>\<lhd>\<^sub>\<Gamma> v \<and> \<phi> v"
abbreviation c20::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("[_]\<^sup>\<prec>_") where "[\<Gamma>]\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<forall>v. w \<^bold>\<lhd>\<^sub>\<Gamma> v \<longrightarrow> \<phi> v"
abbreviation c21::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<langle>_\<^bold>\<rangle>_")  where "\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi> \<equiv> \<lambda>w.\<exists>v. w \<^bold>\<equiv>\<^sub>\<Gamma> v \<and> \<phi> v"
abbreviation c22::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("[_]_")  where "[\<Gamma>]\<phi> \<equiv> \<lambda>w.\<forall>v. w \<^bold>\<equiv>\<^sub>\<Gamma> v \<longrightarrow> \<phi> v"

(**** Section 6: Ceteris Paribus Counterparts of Binary Preference Statements ****)
(*Note: operators below are not defined in the paper; their existence is tacitly 
  suggested. AA-variant is drawing upon von Wright's*)
type_synonym \<epsilon> = "\<sigma>\<Rightarrow>\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
abbreviation lAA_cp::\<epsilon> ("_\<prec>\<^sub>A\<^sub>A\<^sup>__") where "(\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s.\<forall>t. \<phi> s \<and> \<psi> t \<longrightarrow> s \<^bold>\<lhd>\<^sub>\<Gamma> t"
abbreviation lqAA_cp::\<epsilon> ("_\<preceq>\<^sub>A\<^sub>A\<^sup>__") where "(\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s.\<forall>t. \<phi> s \<and> \<psi> t \<longrightarrow> s \<^bold>\<unlhd>\<^sub>\<Gamma> t" 
abbreviation lAE_cp::\<epsilon> ("_\<prec>\<^sub>A\<^sub>E\<^sup>__") where "(\<phi> \<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s.\<exists>t. \<phi> s \<longrightarrow> \<psi> t \<and> s \<^bold>\<lhd>\<^sub>\<Gamma> t" 
abbreviation lqAE_cp::\<epsilon> ("_\<preceq>\<^sub>A\<^sub>E\<^sup>__") where "(\<phi> \<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s.\<exists>t. \<phi> s \<longrightarrow> \<psi> t \<and> s \<^bold>\<unlhd>\<^sub>\<Gamma> t" 
abbreviation lAA_cp'::\<epsilon> ("_\<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>__") where "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<psi> \<^bold>\<rightarrow> [\<Gamma>]\<^sup>\<preceq>\<^bold>\<not>\<phi>)"
abbreviation lqAA_cp'::\<epsilon> ("_\<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>__") where "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<and> [\<Gamma>]\<^sup>\<prec>\<^bold>\<not>\<psi>)"
abbreviation lAE_cp'::\<epsilon>  ("_\<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>__") where "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<psi>)" 
abbreviation lqAE_cp'::\<epsilon> ("_\<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>__") where "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<psi>)"

(*Consistency confirmed (trivial: essentially only abbreviations are introduced*)
lemma True nitpick[satisfy,user_axioms] oops
end

(* Lines 80--92: Except for $<^\Gamma$, the operators defined here are not explicitly 
defined in the paper, but their existence is tacitly suggested. $<^\Gamma$ aims at 
modelling von Wright's notion of ceteris paribus (``all other things being equal'') 
preferences wrt. a set of formulas $\Gamma$ and it corresponds to $<_{AA}^\Sigma$ 
below, where $\Sigma=cp(\Gamma)$, i.e., $\Sigma$ are the propositional atoms 
independent from (not occurring in)  $\Gamma$, they are to be elicited by 
extra-logical means. Our variants below can thus be understood as "these (given) 
things being equal"-preferences. *)

