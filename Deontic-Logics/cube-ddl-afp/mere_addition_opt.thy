section \<open>Study Mere Addition Paradox: opt rule\<close>

text \<open>This section studies the mere addition scenario \cite{Parfit1984-PARRAP,ddl:T87} when assuming the opt rule.\<close>

theory mere_addition_opt  (* Christoph Benzmüller, Xavier Parent, 2024  *)
imports DDLcube

begin

consts A::\<sigma> Aplus::\<sigma> B::\<sigma>

axiomatization where
 \<comment>\<open>A is striclty better than B\<close>
 P0: "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>)\<rfloor>" and
 \<comment>\<open>Aplus is at least as good as A\<close>
 P1: "\<lfloor>\<^bold>\<not>\<odot><\<^bold>\<not>Aplus|A\<^bold>\<or>Aplus>\<rfloor>" and
 \<comment>\<open>B is strictly better than Aplus\<close>
 P2: "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|Aplus\<^bold>\<or>B> \<^bold>\<and> \<odot><\<^bold>\<not>Aplus|Aplus\<^bold>\<or>B>)\<rfloor>"

text \<open>Sledgehammer finds P0-P2 inconsistent given transitivity of the betterness relation in the models.\<close>

theorem T0:
  assumes transitivity
  shows False 
  \<comment>\<open>sledgehammer\<close>
  by (metis P0 P1 P2 assms)

text \<open>Nitpick shows consistency in the absence of transitivity.\<close>

theorem T1:
  True
  nitpick [satisfy,expect=genuine,card i=3]  \<comment>\<open>model found\<close>
  oops

text \<open>Sledgehammer confirms inconsistency in the presence of the interval order condition.\<close>

theorem T2:
  assumes reflexivity Ferrers
  shows False
  \<comment>\<open>sledgehammer\<close>
  by (metis P0 P1 P2 assms(2))
  
text \<open>Nitpick shows consistency if transitivity is weakened into acyclicity or quasi-transitivity.\<close>

theorem T3:
  assumes loopfree
  shows True
  nitpick [satisfy,expect=genuine,card=3]  \<comment>\<open>model found\<close> 
  oops

theorem T4:
  assumes Quasitransit
  shows True
  nitpick [satisfy,expect=genuine,card=4]  \<comment>\<open>model found\<close>
  oops

end



















  