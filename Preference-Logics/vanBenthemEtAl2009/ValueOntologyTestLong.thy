theory ValueOntologyTestLong (** Benzmüller, Fuenmayor & Lomfeld, 2020 **)  
  imports ValueOntology
begin 
lemma "True" nitpick[satisfy,show_all,card i=10] oops
lemma "\<lfloor>INCONS\<^sup>p\<rfloor>" nitpick[satisfy,card i=4] nitpick oops (*contingent*)
(*ext/int operators satisfy main properties of Galois connections*)
lemma G:      "B \<^bold>\<sqsubseteq> A\<up> \<longleftrightarrow> A \<^bold>\<sqsubseteq> B\<down>" by blast
lemma G1:     "A \<^bold>\<sqsubseteq> A\<up>\<down>" by simp
lemma G2:     "B \<^bold>\<sqsubseteq> B\<down>\<up>" by simp
lemma G3:     "A\<^sub>1 \<^bold>\<sqsubseteq> A\<^sub>2 \<longrightarrow> A\<^sub>2\<up> \<^bold>\<sqsubseteq> A\<^sub>1\<up>" by simp
lemma G4:     "B\<^sub>1 \<^bold>\<sqsubseteq> B\<^sub>2 \<longrightarrow> B\<^sub>2\<down> \<^bold>\<sqsubseteq> B\<^sub>1\<down>" by simp
lemma cl1:    "A\<up> = A\<up>\<down>\<up>" by blast
lemma cl2:    "B\<down> = B\<down>\<up>\<down>" by blast
lemma dual1a: "(A\<^sub>1 \<^bold>\<squnion> A\<^sub>2)\<up> = (A\<^sub>1\<up> \<^bold>\<sqinter> A\<^sub>2\<up>)" by blast
lemma dual1b: "(B\<^sub>1 \<^bold>\<squnion> B\<^sub>2)\<down> = (B\<^sub>1\<down> \<^bold>\<sqinter> B\<^sub>2\<down>)" by blast
lemma         "(A\<^sub>1 \<^bold>\<sqinter> A\<^sub>2)\<up> \<^bold>\<sqsubseteq> (A\<^sub>1\<up> \<^bold>\<squnion> A\<^sub>2\<up>)" nitpick oops
lemma         "(B\<^sub>1 \<^bold>\<sqinter> B\<^sub>2)\<down> \<^bold>\<sqsubseteq> (B\<^sub>1\<down> \<^bold>\<squnion> B\<^sub>2\<down>)" nitpick oops
lemma dual2a: "(A\<^sub>1\<up> \<^bold>\<squnion> A\<^sub>2\<up>) \<^bold>\<sqsubseteq>  (A\<^sub>1 \<^bold>\<sqinter> A\<^sub>2)\<up>" by blast
lemma dual2b: "(B\<^sub>1\<down> \<^bold>\<squnion> B\<^sub>2\<down>) \<^bold>\<sqsubseteq>  (B\<^sub>1 \<^bold>\<sqinter> B\<^sub>2)\<down>" by blast
(*Note: two different but logically equivalent notations*)
lemma "[WILL\<^sup>x] \<equiv> WILL\<^sup>x\<down>" by simp
lemma "[WILL\<^sup>x\<oplus>STAB\<^sup>x] \<equiv> (WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x)\<down>" by simp
(********* value ontology tests *****************)
lemma "\<lfloor>[RELI\<^sup>p] \<^bold>\<and> [WILL\<^sup>p] \<^bold>\<rightarrow> INCONS\<^sup>p\<rfloor>" by simp 
lemma "\<lfloor>INCONS\<^sup>p \<^bold>\<rightarrow> [RELI\<^sup>p] \<^bold>\<and> [WILL\<^sup>p]\<rfloor>" by simp 
lemma "\<lfloor>[RELI\<^sup>p] \<^bold>\<and> [WILL\<^sup>p]\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>[FAIR\<^sup>d] \<^bold>\<and> [EFFI\<^sup>d]\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(\<^bold>\<not>INCONS\<^sup>p) \<^bold>\<and> [FAIR\<^sup>d] \<^bold>\<and> [EFFI\<^sup>d]\<rfloor>"
 nitpick[satisfy,show_all] nitpick oops (*contingent: p & d independent*)
lemma "\<lfloor>(\<^bold>\<not>INCONS\<^sup>d) \<^bold>\<and> (\<^bold>\<not>INCONS\<^sup>p) \<^bold>\<and> [RELI\<^sup>d] \<^bold>\<and> [WILL\<^sup>p]\<rfloor>" 
 nitpick[satisfy,show_all] nitpick oops (*contingent: p & d independent*)
(*** more tests ***)
(*values in two non-opposed quadrants (noq): consistent*)
lemma "\<lfloor>[WILL\<^sup>x] \<^bold>\<and> [STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*countermodel found*)
lemma "\<lfloor>[WILL\<^sup>x] \<^bold>\<and> [GAIN\<^sup>x] \<^bold>\<and> [EFFI\<^sup>x] \<^bold>\<and> [STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops
(*values in two opposed quadrants: inconsistent*)
lemma "\<lfloor>[RESP\<^sup>x] \<^bold>\<and> [STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by simp
(*values in three quadrants: inconsistent*)
lemma "\<lfloor>[WILL\<^sup>x] \<^bold>\<and> [EFFI\<^sup>x] \<^bold>\<and> [RELI\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by simp
(*values in opposed quadrants for different parties: consistent*)
lemma "\<lfloor>[EQUI\<^sup>x] \<^bold>\<and> [GAIN\<^sup>y] \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*cntmdl*)
lemma "\<lfloor>[RESP\<^sup>x] \<^bold>\<and> [STAB\<^sup>y] \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*cntmdl*)
(*value preferences tests*)
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor>"
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v STAB\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor>" by blast
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v STAB\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor>" by blast
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v STAB\<^sup>x\<rfloor>"
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v STAB\<^sup>x\<rfloor>"
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<not>\<lfloor>WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" using rBR by auto
lemma "\<lfloor>WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" by auto
lemma "\<lfloor>RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" by auto
lemma "\<lfloor>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
(*basic properties*)
lemma "\<lfloor>\<^bold>\<not>(X \<^bold>\<prec>\<^sub>v X)\<rfloor>" using rBR by auto (*irreflexive*)
lemma "\<lfloor>X \<^bold>\<prec>\<^sub>v Y \<^bold>\<rightarrow> \<^bold>\<not>(Y \<^bold>\<prec>\<^sub>v X)\<rfloor>" nitpick oops (*not asymmetric*)
lemma "\<lfloor>(X \<^bold>\<prec>\<^sub>v Y \<^bold>\<and> Y \<^bold>\<prec>\<^sub>v Z) \<^bold>\<rightarrow> X \<^bold>\<prec>\<^sub>v Z\<rfloor>" nitpick oops (*not transitive*)
end

