section \<open>Study Mere Addition Paradox:: Lewis' rule\<close>

text \<open>This section studies the mere addition scenario \cite{Parfit1984-PARRAP,ddl:T87} when assuming the Lewis rule.\<close>

theory mere_addition_lewis  (* Christoph Benzmüller, Xavier Parent, 2024  *)
imports DDLcube

begin

consts a::\<sigma> aplus::\<sigma> b::\<sigma>

axiomatization where
 \<comment>\<open>A is striclty better than B\<close>
 PPP0: "\<lfloor>(\<^bold>\<not>\<circ><\<^bold>\<not>a|a\<^bold>\<or>b>\<^bold>\<and>\<circ><\<^bold>\<not>b|a\<^bold>\<or>b>)\<rfloor>" and
 \<comment>\<open>Aplus is at least as good as A\<close>
 PPP1: "\<lfloor>\<^bold>\<not>\<circ><\<^bold>\<not>aplus|a\<^bold>\<or>aplus>\<rfloor>" and
 \<comment>\<open>B is strictly better than Aplus\<close>
 PPP2: "\<lfloor>(\<^bold>\<not>\<circ><\<^bold>\<not>b|aplus\<^bold>\<or>b> \<^bold>\<and> \<circ><\<^bold>\<not>aplus|aplus\<^bold>\<or>b>)\<rfloor>"

text \<open>Sledgehammer finds PPP0-PPP2 inconsistent given transitivity of the betterness relation in the models.\<close>

theorem T0:
  assumes transitivity
  shows False 
  \<comment>\<open>sledgehammer\<close>
  by (metis PPP0 PPP1 PPP2 assms)
  
text \<open>Nitpick shows consistency in the absence of transitivity.\<close>

lemma T1:
  True
  nitpick [satisfy,expect=genuine,card i=3,show_all] \<comment>\<open>model found\<close>
  oops

text \<open>Sledgehammer confirms inconsistency in the presence of the interval order condition.\<close>

theorem T2:
  assumes reflexivity Ferrers
  shows False
  \<comment>\<open>sledgehammer\<close>
  by (metis PPP0 PPP1 PPP2 assms(1) assms(2)) 
  
text \<open>Nitpick shows consistency if transitivity is weakened into acyclicity
 or quasi-transitivity.\<close>

theorem T3:
  assumes loopfree
  shows True
  nitpick [satisfy,expect=genuine,card=3] \<comment>\<open>model found\<close>
  oops

theorem T4:
  assumes Quasitransit
  shows True
  nitpick [satisfy,expect=genuine,card=4] \<comment>\<open>model found\<close>
  oops

end



















  