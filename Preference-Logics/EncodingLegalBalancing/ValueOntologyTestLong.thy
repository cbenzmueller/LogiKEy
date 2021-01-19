theory ValueOntologyTestLong imports ValueOntology (** Benzmüller, Fuenmayor & Lomfeld, 2021 **)  
begin 
lemma "True" nitpick[satisfy,show_all,card \<iota>=10] oops
lemma "\<lfloor>Conflict\<^sup>p\<rfloor>" nitpick[satisfy,card \<iota>=4] nitpick oops (*contingent*)
 (*derivation operators satisfy main properties of Galois connections*)
lemma G:      "B \<^bold>\<sqsubseteq> A\<up> \<longleftrightarrow> A \<^bold>\<sqsubseteq> B\<down>" by blast
lemma G1:     "A \<^bold>\<sqsubseteq> A\<up>\<down>" by simp
lemma G2:     "B \<^bold>\<sqsubseteq> B\<down>\<up>" by simp
lemma G3:     "A\<^sub>1 \<^bold>\<sqsubseteq> A\<^sub>2 \<longrightarrow> A\<^sub>2\<up> \<^bold>\<sqsubseteq> A\<^sub>1\<up>" by simp
lemma G4:     "B\<^sub>1 \<^bold>\<sqsubseteq> B\<^sub>2 \<longrightarrow> B\<^sub>2\<down> \<^bold>\<sqsubseteq> B\<^sub>1\<down>" by simp
lemma cl1:    "A\<up> = A\<up>\<down>\<up>" by blast
lemma cl2:    "B\<down> = B\<down>\<up>\<down>" by blast
lemma dual1a: "(A\<^sub>1 \<^bold>\<squnion> A\<^sub>2)\<up> = (A\<^sub>1\<up> \<^bold>\<sqinter> A\<^sub>2\<up>)" by blast
lemma dual1b: "(B\<^sub>1 \<^bold>\<squnion> B\<^sub>2)\<down> = (B\<^sub>1\<down> \<^bold>\<sqinter> B\<^sub>2\<down>)" by blast
lemma         "(A\<^sub>1 \<^bold>\<sqinter> A\<^sub>2)\<up> \<^bold>\<sqsubseteq> (A\<^sub>1\<up> \<^bold>\<squnion> A\<^sub>2\<up>)" nitpick oops (*countermodel*)
lemma         "(B\<^sub>1 \<^bold>\<sqinter> B\<^sub>2)\<down> \<^bold>\<sqsubseteq> (B\<^sub>1\<down> \<^bold>\<squnion> B\<^sub>2\<down>)" nitpick oops (*countermodel*)
lemma dual2a: "(A\<^sub>1\<up> \<^bold>\<squnion> A\<^sub>2\<up>) \<^bold>\<sqsubseteq>  (A\<^sub>1 \<^bold>\<sqinter> A\<^sub>2)\<up>" by blast
lemma dual2b: "(B\<^sub>1\<down> \<^bold>\<squnion> B\<^sub>2\<down>) \<^bold>\<sqsubseteq>  (B\<^sub>1 \<^bold>\<sqinter> B\<^sub>2)\<down>" by blast
 (*value conflict tests*)
lemma "\<lfloor>[RELI\<^sup>p] \<^bold>\<and> [WILL\<^sup>p] \<^bold>\<rightarrow> Conflict\<^sup>p\<rfloor>" by simp 
lemma "\<lfloor>Conflict\<^sup>p \<^bold>\<rightarrow> [RELI\<^sup>p] \<^bold>\<and> [WILL\<^sup>p]\<rfloor>" by simp 
lemma "\<lfloor>[RELI\<^sup>p] \<^bold>\<and> [WILL\<^sup>p]\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>[FAIR\<^sup>d] \<^bold>\<and> [EFFI\<^sup>d]\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(\<^bold>\<not>Conflict\<^sup>p) \<^bold>\<and> [FAIR\<^sup>d] \<^bold>\<and> [EFFI\<^sup>d]\<rfloor>"
 nitpick[satisfy,show_all] nitpick oops (*contingent: p & d independent*)
lemma "\<lfloor>(\<^bold>\<not>Conflict\<^sup>d) \<^bold>\<and> (\<^bold>\<not>Conflict\<^sup>p) \<^bold>\<and> [RELI\<^sup>d] \<^bold>\<and> [WILL\<^sup>p]\<rfloor>" 
 nitpick[satisfy,show_all] nitpick oops (*contingent: p & d independent*)
 (*values in two non-opposed quadrants: no conflict*)
lemma "\<lfloor>[WILL\<^sup>x] \<^bold>\<and> [STAB\<^sup>x] \<^bold>\<rightarrow> Conflict\<^sup>x\<rfloor>" nitpick oops (*countermodel found*)
lemma "\<lfloor>[WILL\<^sup>x] \<^bold>\<and> [GAIN\<^sup>x] \<^bold>\<and> [EFFI\<^sup>x] \<^bold>\<and> [STAB\<^sup>x] \<^bold>\<rightarrow> Conflict\<^sup>x\<rfloor>" nitpick oops
 (*values in two opposed quadrants: conflict*)
lemma "\<lfloor>[RESP\<^sup>x] \<^bold>\<and> [STAB\<^sup>x] \<^bold>\<rightarrow> Conflict\<^sup>x\<rfloor>" by simp
 (*values in three quadrants: conflict*)
lemma "\<lfloor>[WILL\<^sup>x] \<^bold>\<and> [EFFI\<^sup>x] \<^bold>\<and> [RELI\<^sup>x] \<^bold>\<rightarrow> Conflict\<^sup>x\<rfloor>" by simp
 (*values in opposed quadrants for different parties: no conflict*)
lemma "\<lfloor>[EQUI\<^sup>x] \<^bold>\<and> [GAIN\<^sup>y] \<^bold>\<rightarrow> (Conflict\<^sup>x \<^bold>\<or> Conflict\<^sup>y)\<rfloor>" nitpick oops (*cntmdl*)
lemma "\<lfloor>[RESP\<^sup>x] \<^bold>\<and> [STAB\<^sup>y] \<^bold>\<rightarrow> (Conflict\<^sup>x \<^bold>\<or> Conflict\<^sup>y)\<rfloor>" nitpick oops (*cntmdl*)
 (*value preferences tests*)
lemma "\<lfloor>[WILL\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<rfloor>" nitpick nitpick[satisfy] oops (*contingent*) 
lemma "\<lfloor>[WILL\<^sup>x]\<^bold>\<prec>[STAB\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[WILL\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<rfloor>" by blast
lemma "\<lfloor>[WILL\<^sup>x]\<^bold>\<prec>[STAB\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[WILL\<^sup>x]\<^bold>\<prec>[RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<rfloor>" by blast
lemma "\<lfloor>[WILL\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[WILL\<^sup>x]\<^bold>\<prec>[STAB\<^sup>x]\<rfloor>" (*nitpick*) nitpick[satisfy] oops (*ctgnt?*)
lemma "\<lfloor>[WILL\<^sup>x]\<^bold>\<prec>[RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[WILL\<^sup>x]\<^bold>\<prec>[STAB\<^sup>x]\<rfloor>" nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>[WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x]\<rfloor>" nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>[WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[STAB\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x]\<rfloor>" by metis
lemma "\<lfloor>[RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[STAB\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x]\<rfloor>" by metis
lemma "\<lfloor>[STAB\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x]\<rfloor>" nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>[STAB\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<^bold>\<prec>[WILL\<^sup>x]\<rfloor>" nitpick nitpick[satisfy] oops (*contingent*)
 (*basic properties*)
lemma "\<lfloor>[X]\<^bold>\<prec>[X]\<rfloor>" nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>(([X]\<^bold>\<prec>[Y]) \<^bold>\<and> ([Y]\<^bold>\<prec>[Z])) \<^bold>\<rightarrow> ([X]\<^bold>\<prec>[Z])\<rfloor>" using tSBR by blast (*transitive*)
lemma "\<lfloor>([X]\<^bold>\<prec>[Y]) \<^bold>\<and> ([Y]\<^bold>\<prec>[X])\<rfloor> \<longrightarrow> X = Y" nitpick oops (*not antisymmetric*)
end

