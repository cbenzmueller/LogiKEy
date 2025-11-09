section \<open>Study Mere Addition Paradox: max rule\<close>

text \<open>This section studies the mere addition scenario \cite{Parfit1984-PARRAP,ddl:T87} when assuming the max rule.\<close>

theory mere_addition_max  (* Christoph Benzmüller, Xavier Parent, 2024  *)
imports DDLcube

begin

consts A::\<sigma> Aplus::\<sigma> B::\<sigma>  i1::i i2::i i3::i i4::i i5::i i6::i i7::i i8::i 

axiomatization where
 \<comment>\<open>A is striclty better than B\<close>
 PP0: "\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>A|A\<^bold>\<or>B>\<^bold>\<and>\<circle><\<^bold>\<not>B|A\<^bold>\<or>B>)\<rfloor>" and
 \<comment>\<open>Aplus is at least as good as A\<close>
 PP1: "\<lfloor>\<^bold>\<not>\<circle><\<^bold>\<not>Aplus|A\<^bold>\<or>Aplus>\<rfloor>" and
 \<comment>\<open>B is strictly better than Aplus\<close>
 PP2: "\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>B|Aplus\<^bold>\<or>B> \<^bold>\<and> \<circle><\<^bold>\<not>Aplus|Aplus\<^bold>\<or>B>)\<rfloor>" 


text \<open>Nitpick finds no finite model for the betterness 
   relation.\<close>

theorem T0:
  assumes transitivity  
  shows True
  nitpick [satisfy] \<comment>\<open>no model found\<close>
  oops  

text \<open>Nitpick shows consistency in the absence of transitivity.\<close>

theorem T1:
  shows True
  nitpick [satisfy,expect=genuine,card i=3]  \<comment>\<open>model found\<close>
  oops

text \<open>Sledgehammer confirms inconsistency in the presence of the interval order condition.\<close>

theorem T2:
  assumes reflexivity and Ferrers
  shows False
  \<comment>\<open>sledgehammer\<close>
  by (metis PP0 PP1 PP2 assms(1) assms(2))
  
text \<open>Nitpick shows consistency if transitivity is weakened into acyclicity.\<close>

theorem T3:
  assumes loopfree
  shows True
  nitpick [satisfy,expect=genuine,card=3] \<comment>\<open>model found\<close>
  oops

text \<open>Transitivity or quasi-transitivity: Nitpick shows inconsistency assuming a finite model
   of cardinality (up to) seven (if we provide the exact dependencies); for higher cardinalities 
   it returns a time out (depending on computing it may prove falsity also for cardinality eight, 
   etc.\<close>

theorem T4:
    assumes
      transitivity and
      OnlyOnes: "\<forall>y. y=i1 \<or> y=i2 \<or> y=i3 \<or> y=i4 \<or> y= i5 \<or> y= i6 \<or> y= i7"
    shows False
    using assfactor_def PP0 PP1 PP2 assms 
  \<comment>\<open>sledgehammer()\<close> 
  \<comment>\<open>proof found by Sledgehammer, but reconstruction fails\<close>
  oops

theorem T5:
    assumes
      Quasitransit and
      OnlyOnes: "\<forall>y. y=i1 \<or> y=i2 \<or> y=i3 \<or> y=i4 \<or> y= i5 \<or> y= i6 \<or> y=i7"
    shows False
  using assfactor_def PP0 PP1 PP2 assms
  \<comment>\<open>sledgehammer()\<close>
  \<comment>\<open>proof found by Sledgehammer, but reconstruction fails\<close>
  oops

text \<open>Testing whether infinity holds — infinity is defined as: there is a surjective mapping G from 
   domain i to a proper subset M of domain i.\<close>

abbreviation "infinity \<equiv> \<exists>M. (\<exists>z::i. \<not>(M z) \<and> (\<exists>G. (\<forall>y::i. (\<exists>x. (M x) \<and> (G x) = y))))"

lemma "infinity" nitpick[expect=genuine] oops \<comment>\<open>countermodel found\<close>

text \<open>Now we study infinity under the assumption of (quasi-)transitivity: we do 
not get any finite countermodels reported anymore.\<close>

lemma 
  assumes transitivity
  shows   infinity
  \<comment>\<open>nitpick\<close>   \<comment>\<open>no countermodel found anymore; nitpicks runs out of time\<close>
  \<comment>\<open>sledgehammer\<close>  \<comment>\<open>but the provers are still too weak to prove it automatically\<close>
  oops

lemma 
  assumes Quasitransit 
  shows   infinity
  \<comment>\<open>nitpick\<close>   \<comment>\<open>no countermodel found anymore; nitpicks runs out of time\<close>
  \<comment>\<open>sledgehammer\<close>  \<comment>\<open>but the provers are still too weak to prove it automatically\<close>
   oops

theorem T0':
  assumes transitivity and totality  
  shows False
  \<comment>\<open>sledgehammer\<close>
  by (metis PP0 PP1 PP2 assms(1) assms(2)) 
  
end
