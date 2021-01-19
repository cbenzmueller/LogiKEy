theory ValueOntologyTest imports ValueOntology (*** Benzmüller, Fuenmayor & Lomfeld, 2021 ***)  
begin 
 (*value principles in two opposed quadrants: conflict*)
lemma "\<lfloor>[RESP\<^sup>x] \<^bold>\<and> [STAB\<^sup>x] \<^bold>\<rightarrow> Conflict\<^sup>x\<rfloor>" by simp (*proof*)
lemma "\<lfloor>[RELI\<^sup>x] \<^bold>\<and> [WILL\<^sup>x] \<^bold>\<rightarrow> Conflict\<^sup>x\<rfloor>" by simp (*proof*)
 (*value principles in two non-opposed quadrants: no conflict*)
lemma "\<lfloor>[WILL\<^sup>x] \<^bold>\<and> [STAB\<^sup>x] \<^bold>\<rightarrow> Conflict\<^sup>x\<rfloor>" nitpick oops (*countermodel*)
 (*value principles in opposed quadrants for different parties: no conflict*)
lemma "\<lfloor>[EQUI\<^sup>x] \<^bold>\<and> [GAIN\<^sup>y] \<^bold>\<rightarrow> (Conflict\<^sup>x \<^bold>\<or> Conflict\<^sup>y)\<rfloor>" nitpick oops (*countermodel*)
lemma "\<lfloor>[RESP\<^sup>x] \<^bold>\<and> [STAB\<^sup>y] \<^bold>\<rightarrow> (Conflict\<^sup>x \<^bold>\<or> Conflict\<^sup>y)\<rfloor>" nitpick oops (*countermodel*)
lemma "\<lfloor>[RELI\<^sup>p] \<^bold>\<and> [WILL\<^sup>p]\<rfloor>" nitpick nitpick[satisfy,card \<iota>=1] oops (*contingent: countermodel and model*)
 (*value aggregation properties*)
lemma "[A\<^bold>\<oplus>B] w \<longrightarrow> (A \<^bold>\<sqinter> B)\<down> w" by simp
lemma "[A\<^bold>\<oplus>B] w \<longrightarrow> A\<down> w" nitpick nitpick[satisfy] oops (*contingent: countermodel and model*)
lemma "\<lfloor>[WILL\<^sup>x] \<^bold>\<prec> [STAB\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[WILL\<^sup>x] \<^bold>\<prec> [RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<rfloor>" by blast (*proof*)
lemma "\<lfloor>[RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x] \<^bold>\<prec> [WILL\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[STAB\<^sup>x] \<^bold>\<prec> [WILL\<^sup>x]\<rfloor>" by metis (*proof*)
lemma "\<lfloor>[WILL\<^sup>x] \<^bold>\<prec> [RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[WILL\<^sup>x] \<^bold>\<prec> [STAB\<^sup>x]\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent: countermodel and model*)
lemma "\<lfloor>[STAB\<^sup>x] \<^bold>\<prec> [WILL\<^sup>x]\<rfloor> \<longrightarrow> \<lfloor>[RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x] \<^bold>\<prec> [WILL\<^sup>x]\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent: countermodel and model*)
end

