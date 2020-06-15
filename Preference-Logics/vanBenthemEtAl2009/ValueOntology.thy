theory ValueOntology     (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports PreferenceLogicBasics 
begin
(*two legal parties (there can be more in principle)*)
datatype c = p | d (*parties/contenders: plaintiff, defendant*)
fun other::"c\<Rightarrow>c" ("_\<inverse>") where "p\<inverse> = d" | "d\<inverse>= p" 
  
consts For::"c\<Rightarrow>\<sigma>"    (*decision: find/rule for party*)
axiomatization where ForAx: "\<lfloor>For x \<^bold>\<leftrightarrow> (\<^bold>\<not>For x\<inverse>)\<rfloor>"

(*ethico-legal values/principles*) 
datatype 
   VAL = WILL | RELI | RESP | EQUI | FAIR | EFFI | STAB | GAIN 
consts V::"c\<Rightarrow> VAL\<Rightarrow>\<sigma>" ("_\<upharpoonleft>_") 
           (*c\<up>UV: (a decision for) party c promotes value V*)

(*useful shorthand notation for aggregated values*) 
abbreviation Agg2 ("_\<upharpoonleft>[_\<oplus>_]") where "c\<upharpoonleft>[V1\<oplus>V2] \<equiv> c\<upharpoonleft>V1 \<^bold>\<and> c\<upharpoonleft>V2"
abbreviation Agg3 ("_\<upharpoonleft>[_\<oplus>_\<oplus>_]")
     where    "c\<upharpoonleft>[V1\<oplus>V2\<oplus>V3] \<equiv> c\<upharpoonleft>V1 \<^bold>\<and> c\<upharpoonleft>V2 \<^bold>\<and> c\<upharpoonleft>V3"
abbreviation Agg4 ("_\<upharpoonleft>[_\<oplus>_\<oplus>_\<oplus>_]") 
     where "c\<upharpoonleft>[V1\<oplus>V2\<oplus>V3\<oplus>V4] \<equiv> c\<upharpoonleft>V1 \<^bold>\<and> c\<upharpoonleft>V2 \<^bold>\<and> c\<upharpoonleft>V3 \<^bold>\<and> c\<upharpoonleft>V4"


abbreviation "SECURITY x \<equiv> (x\<upharpoonleft>RELI \<^bold>\<or> x\<upharpoonleft>EQUI \<^bold>\<or> x\<upharpoonleft>STAB \<^bold>\<or> x\<upharpoonleft>EFFI)"
abbreviation "EQUALITY x \<equiv> (x\<upharpoonleft>FAIR \<^bold>\<or> x\<upharpoonleft>RESP \<^bold>\<or> x\<upharpoonleft>EQUI \<^bold>\<or> x\<upharpoonleft>RELI)"
abbreviation "LIBERTY x \<equiv> (x\<upharpoonleft>WILL \<^bold>\<or> x\<upharpoonleft>GAIN \<^bold>\<or> x\<upharpoonleft>RESP \<^bold>\<or> x\<upharpoonleft>FAIR)"
abbreviation "UTILITY x \<equiv> (x\<upharpoonleft>EFFI \<^bold>\<or> x\<upharpoonleft>STAB \<^bold>\<or> x\<upharpoonleft>GAIN \<^bold>\<or> x\<upharpoonleft>WILL)"
abbreviation "INCONS x \<equiv> 
              (SECURITY x \<^bold>\<and> EQUALITY x \<^bold>\<and> LIBERTY x \<^bold>\<and> UTILITY x)"

(*some useful settings for model finder: enforce information*)
nitpick_params [eval=INCONS SECURITY EQUALITY LIBERTY UTILITY V] 

(*exploring the consistency and models of the ontology*)
lemma "True" nitpick[satisfy,show_all,card i=1] oops
lemma "True" nitpick[satisfy,show_all,card i=3] oops

(*exploring implied knowledge*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" 
  nitpick oops (*two non-opposed quadrants \<oplus> (noq): consistent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>GAIN\<oplus>EFFI\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" 
  nitpick oops (*two noq \<oplus>: consistent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>EFFI\<oplus>RELI] \<^bold>\<rightarrow> INCONS x\<rfloor>" 
  by simp (*three quadrants \<oplus>: inconsistent*)
lemma "\<lfloor>x\<upharpoonleft>[RESP\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" 
  by simp (*two opposed quadrants \<oplus> (oq): inconsistent*)
lemma "\<lfloor>x\<upharpoonleft>EQUI \<^bold>\<and> y\<upharpoonleft>EFFI \<^bold>\<rightarrow> (INCONS x \<^bold>\<or> INCONS y)\<rfloor>" 
  nitpick oops (*two noq (different parties): consistent*)
lemma "\<lfloor>x\<upharpoonleft>RESP \<^bold>\<and> y\<upharpoonleft>STAB \<^bold>\<rightarrow> (INCONS x \<^bold>\<or> INCONS y)\<rfloor>" 
  nitpick oops (*two oq (different parties): consistent*)
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>STAB\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>STAB\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>[RELI\<oplus>STAB]\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>WILL\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>x\<upharpoonleft>WILL \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>STAB\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>WILL \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>[RELI\<oplus>STAB]\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>STAB\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>WILL \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>[RELI\<oplus>STAB]\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<prec>\<^sub>A\<^sub>E x\<upharpoonleft>RELI\<rfloor>" by blast
end

