theory ValueOntologyTest  (*** Benzmüller, Fuenmayor & Lomfeld, 2020 ***)  
  imports ValueOntology
begin (* value ontology tests *)
(*values in two opposed quadrants: inconsistent*)
lemma "\<lfloor>[RESP\<^sup>x] \<^bold>\<and> [STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by simp
lemma "\<lfloor>[RELI\<^sup>x] \<^bold>\<and> [WILL\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by simp
(*all values in two non-opposed quadrants: consistent*)
lemma "\<lfloor>[WILL\<^sup>x] \<^bold>\<and> [STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops  (*countermodel*)
(*values in opposed quadrants for different parties: consistent*)
lemma "\<lfloor>[EQUI\<^sup>x] \<^bold>\<and> [GAIN\<^sup>y] \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*ctmdl*)
lemma "\<lfloor>[RESP\<^sup>x] \<^bold>\<and> [STAB\<^sup>y] \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*ctmdl*)
lemma "\<lfloor>[RELI\<^sup>p] \<^bold>\<and> [WILL\<^sup>p]\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
(*value preferences tests*)
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v STAB\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor>" by blast
lemma "\<lfloor>RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" by auto
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v STAB\<^sup>x\<rfloor>"
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
end

