theory ValueOntologyTest  (*** Benzmüller, Fuenmayor & Lomfeld, 2020 ***)  
  imports ValueOntology
begin
(*exploring the consistency and models of the ontology*)
lemma "True" nitpick[satisfy,show_all,card i=10] oops
lemma "\<lfloor>INCONS\<^sup>p\<rfloor>" nitpick[satisfy,card i=4] nitpick oops (*contingent*)
lemma "\<lfloor>INDIFF\<^sup>p\<rfloor>" nitpick[satisfy,card i=4] nitpick oops (*contingent*)
(*Ext/Int operators satisfy main properties of Galois connections*)
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
(*both notations do the same. TODO: do we want to do away with rhs?*)
lemma "\<lfloor>[WILL\<^sup>x\<oplus>STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor> \<equiv> \<lfloor>(WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x)\<down> \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by simp
(********* value ontology tests *****************)
lemma "SECURITY\<^sup>x \<^bold>\<sqsubseteq> RELI\<^sup>x" by simp
lemma "RELI\<^sup>x\<down> \<^bold>\<sqsubseteq> SECURITY\<^sup>x\<down>" by simp
lemma "\<lfloor>RELI\<^sup>x\<down> \<^bold>\<rightarrow> SECURITY\<^sup>x\<down>\<rfloor>" by simp
lemma "EQUALITY\<^sup>x \<^bold>\<sqsubseteq> RELI\<^sup>x" by simp
lemma "RELI\<^sup>x\<down> \<^bold>\<sqsubseteq> EQUALITY\<^sup>x\<down>" by simp
lemma "\<lfloor>RELI\<^sup>x\<down> \<^bold>\<rightarrow> EQUALITY\<^sup>x\<down>\<rfloor>" by simp
lemma "\<lfloor>RELI\<^sup>x\<down> \<^bold>\<rightarrow> (SECURITY\<^sup>x\<down> \<^bold>\<and> EQUALITY\<^sup>x\<down>)\<rfloor>" by simp
lemma "\<lfloor>RELI\<^sup>p\<down> \<^bold>\<and> WILL\<^sup>p\<down> \<^bold>\<rightarrow> INCONS\<^sup>p\<rfloor>" by simp 
lemma "\<lfloor>INCONS\<^sup>p \<^bold>\<rightarrow> RELI\<^sup>p\<down> \<^bold>\<and> WILL\<^sup>p\<down>\<rfloor>" by simp 
lemma "\<lfloor>RELI\<^sup>p\<down> \<^bold>\<and> WILL\<^sup>p\<down>\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>FAIR\<^sup>d\<down> \<^bold>\<and> EFFI\<^sup>d\<down>\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(\<^bold>\<not>INCONS\<^sup>p) \<^bold>\<and> [FAIR\<^sup>d] \<^bold>\<and> [EFFI\<^sup>d]\<rfloor>"
 nitpick[satisfy,show_all] nitpick oops (*contingent: p & d independent*)
lemma "\<lfloor>(\<^bold>\<not>INCONS\<^sup>d) \<^bold>\<and> (\<^bold>\<not>INCONS\<^sup>p) \<^bold>\<and> [RELI\<^sup>d] \<^bold>\<and> [WILL\<^sup>p]\<rfloor>" 
 nitpick[satisfy,show_all] nitpick oops (*contingent: p & d independent*)
(*** more tests ***)
(*two non-opposed quadrants \<oplus> (noq): consistent*)
lemma "\<lfloor>[WILL\<^sup>x\<oplus>STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops 
(*two non-opposed quadrants \<and> (noq): consistent*)
lemma "\<lfloor>WILL\<^sup>x\<down> \<^bold>\<and> STAB\<^sup>x\<down> \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops 
lemma "\<lfloor>[WILL\<^sup>x\<oplus>GAIN\<^sup>X\<oplus>EFFI\<^sup>x\<oplus>STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*consistent*)
lemma "\<lfloor>WILL\<^sup>x\<down> \<^bold>\<and> GAIN\<^sup>X\<down> \<^bold>\<and> EFFI\<^sup>x\<down> \<^bold>\<and> STAB\<^sup>x\<down> \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*""*)
lemma "\<lfloor>[WILL\<^sup>x\<oplus>EFFI\<^sup>x\<oplus>RELI\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*consistent*)
lemma "\<lfloor>WILL\<^sup>x\<down> \<^bold>\<and> EFFI\<^sup>x\<down> \<^bold>\<and> RELI\<^sup>x\<down> \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by simp (*inconsistent*)
lemma "\<lfloor>[RESP\<^sup>x\<oplus>STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*consistent*)
lemma "\<lfloor>RESP\<^sup>x\<down> \<^bold>\<and> STAB\<^sup>x\<down> \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by simp (*inconsistent*)
lemma "\<lfloor>[EQUI\<^sup>x\<oplus>EFFI\<^sup>y] \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*consistent*)
lemma "\<lfloor>EQUI\<^sup>x\<down> \<^bold>\<and> EFFI\<^sup>y\<down> \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*consist.*)
lemma "\<lfloor>[RESP\<^sup>x\<oplus>STAB\<^sup>y] \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*consistent*)
lemma "\<lfloor>RESP\<^sup>x\<down> \<^bold>\<and> STAB\<^sup>y\<down> \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*consist.*)
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
end

