theory ValueOntology2  imports PreferenceLogicBasics begin       (*Benzmüller,Fuenmayor & Lomfeld, 2020*)  

datatype c = p | d      (*parties/contenders: plaintiff, defendant*)  
fun other::"c\<Rightarrow>c" ("_\<inverse>") where "p\<inverse> = d" | "d\<inverse>= p" (* there can be more in principle*)
consts For::"c\<Rightarrow>\<sigma>"    (*decision: find/rule for party*)
axiomatization where ForAx: "\<lfloor>For x \<^bold>\<leftrightarrow> (\<^bold>\<not>For x\<inverse>)\<rfloor>"

datatype VAL = WILL | RELI | RESP | EQUI | FAIR | EFFI | STAB | GAIN (*ethico-legal values/principles*) 
consts  V::"c\<Rightarrow> VAL\<Rightarrow>\<sigma>" ("_\<upharpoonleft>_") (*c\<up>UV: (a decision for) party c promotes value V*)

abbreviation V_aggr2::"c\<Rightarrow>VAL\<Rightarrow>VAL\<Rightarrow>\<sigma>" ("_\<upharpoonleft>[_\<oplus>_]") where "c\<upharpoonleft>[V1\<oplus>V2] \<equiv> (c\<upharpoonleft>V1) \<^bold>\<and> (c\<upharpoonleft>V2)"
abbreviation V_aggr3::"c\<Rightarrow>VAL\<Rightarrow>VAL\<Rightarrow>VAL\<Rightarrow>\<sigma>" ("_\<upharpoonleft>[_\<oplus>_\<oplus>_]") where "c\<upharpoonleft>[V1\<oplus>V2\<oplus>V3] \<equiv> (c\<upharpoonleft>V1) \<^bold>\<and> (c\<upharpoonleft>V2) \<^bold>\<and> (c\<upharpoonleft>V3)"
abbreviation V_aggr4::"c\<Rightarrow>VAL\<Rightarrow>VAL\<Rightarrow>VAL\<Rightarrow>VAL\<Rightarrow>\<sigma>" ("_\<upharpoonleft>[_\<oplus>_\<oplus>_\<oplus>_]") where "c\<upharpoonleft>[V1\<oplus>V2\<oplus>V3\<oplus>V4] \<equiv> (c\<upharpoonleft>V1) \<^bold>\<and> (c\<upharpoonleft>V2) \<^bold>\<and> (c\<upharpoonleft>V3) \<^bold>\<and> (c\<upharpoonleft>V4)"
(* ... add more on demand*)

abbreviation "SECURITY x \<equiv> (x\<upharpoonleft>RELI \<^bold>\<or> x\<upharpoonleft>EQUI \<^bold>\<or> x\<upharpoonleft>STAB \<^bold>\<or> x\<upharpoonleft>EFFI)"
abbreviation "EQUALITY x \<equiv> (x\<upharpoonleft>FAIR \<^bold>\<or> x\<upharpoonleft>RESP \<^bold>\<or> x\<upharpoonleft>EQUI \<^bold>\<or> x\<upharpoonleft>RELI)"
abbreviation "LIBERTY x \<equiv> (x\<upharpoonleft>WILL \<^bold>\<or> x\<upharpoonleft>GAIN \<^bold>\<or> x\<upharpoonleft>RESP \<^bold>\<or> x\<upharpoonleft>FAIR)"
abbreviation "UTILITY x \<equiv> (x\<upharpoonleft>EFFI \<^bold>\<or> x\<upharpoonleft>STAB \<^bold>\<or> x\<upharpoonleft>GAIN \<^bold>\<or> x\<upharpoonleft>WILL)"
abbreviation "INCONS x \<equiv> (SECURITY x \<^bold>\<and> EQUALITY x \<^bold>\<and> LIBERTY x \<^bold>\<and> UTILITY x)"

(*exploring & assessing the ontology with automated tools*)
lemma "\<not>(\<exists>(x::i) y z. \<not>(x = y) \<and> \<not>(x = z) \<and> \<not>(y = z))" nitpick oops (*by blast*)
lemma "True" nitpick[satisfy,card i=3] oops

lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" nitpick oops (* 2 non-opposed quadrants \<oplus> (noq): consistent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>GAIN\<oplus>EFFI\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" nitpick oops (* 2 noq \<oplus>: consistent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>EFFI\<oplus>RELI] \<^bold>\<rightarrow> INCONS x\<rfloor>" by simp (* 3 quadrants \<oplus>: inconsistent*)
lemma "\<lfloor>x\<upharpoonleft>[RESP\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" by simp (* 2 opposed quadrants \<oplus> (oq): inconsistent*)
lemma "\<lfloor>x\<upharpoonleft>EQUI \<^bold>\<and> y\<upharpoonleft>EFFI \<^bold>\<rightarrow> (INCONS x \<^bold>\<or> INCONS y)\<rfloor>" nitpick oops (* 2 noq (different parties): consistent*)
lemma "\<lfloor>x\<upharpoonleft>RESP \<^bold>\<and> y\<upharpoonleft>STAB \<^bold>\<rightarrow> (INCONS x \<^bold>\<or> INCONS y)\<rfloor>" nitpick oops (* 2 oq (different parties): consistent*)

lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor>" nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>STAB\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>STAB\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>[RELI\<oplus>STAB]\<rfloor>" by blast

lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>WILL\<rfloor>" nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>x\<upharpoonleft>WILL \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>STAB\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>WILL \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>[RELI\<oplus>STAB]\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>STAB\<rfloor>" by blast

end

