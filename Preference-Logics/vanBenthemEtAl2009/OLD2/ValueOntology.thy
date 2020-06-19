theory ValueOntology     (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports PreferenceLogicBasics 
begin (*** Lomfeld's value ontology is encoded ***)
(*two legal parties (there can be more in principle)*)
datatype c = p | d (*parties/contenders: plaintiff, defendant*)
fun other::"c\<Rightarrow>c" ("_\<inverse>") where "p\<inverse> = d" | "d\<inverse>= p" 
  
consts For::"c\<Rightarrow>\<sigma>"    (*decision: find/rule for party*)
axiomatization where ForAx: "\<lfloor>For x \<^bold>\<leftrightarrow> (\<^bold>\<not>For x\<inverse>)\<rfloor>"

(* abbreviation relPref::\<nu> ("_\<^bold>\<prec>_") where "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E \<psi> " *)
abbreviation relPref::\<nu> ("_\<^bold>\<prec>_") where "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<psi> \<^bold>\<succ>\<^sub>E\<^sub>A \<phi>"

datatype (*ethico-legal values/principles*) 
   VAL = WILL | RELI | RESP | EQUI | FAIR | EFFI | STAB | GAIN 

(*predicate c\<up>UV: (a decision for) party c promotes value V*)
consts V::"c\<Rightarrow>VAL\<Rightarrow>\<sigma>" ("_\<upharpoonleft>_") 

(*upper values and their compliance with ethico-legal values*)
abbreviation "SECURITY x \<equiv> (x\<upharpoonleft>RELI \<^bold>\<or> x\<upharpoonleft>EQUI \<^bold>\<or> x\<upharpoonleft>STAB \<^bold>\<or> x\<upharpoonleft>EFFI)"
abbreviation "EQUALITY x \<equiv> (x\<upharpoonleft>FAIR \<^bold>\<or> x\<upharpoonleft>RESP \<^bold>\<or> x\<upharpoonleft>EQUI \<^bold>\<or> x\<upharpoonleft>RELI)"
abbreviation "LIBERTY x \<equiv> (x\<upharpoonleft>WILL \<^bold>\<or> x\<upharpoonleft>GAIN \<^bold>\<or> x\<upharpoonleft>RESP \<^bold>\<or> x\<upharpoonleft>FAIR)"
abbreviation "UTILITY x \<equiv> (x\<upharpoonleft>EFFI \<^bold>\<or> x\<upharpoonleft>STAB \<^bold>\<or> x\<upharpoonleft>GAIN \<^bold>\<or> x\<upharpoonleft>WILL)"
abbreviation (*inconsistency of upper values*)
 "INCONS x \<equiv> (SECURITY x \<^bold>\<and> EQUALITY x \<^bold>\<and> LIBERTY x \<^bold>\<and> UTILITY x)"
abbreviation (*Indifference*)
 "INDIFF x \<equiv> \<^bold>\<not>(SECURITY x \<^bold>\<or> EQUALITY x \<^bold>\<or> LIBERTY x \<^bold>\<or> UTILITY x)"

(*some useful settings for model finder: enforce information*)
nitpick_params [eval=INCONS SECURITY EQUALITY LIBERTY UTILITY V] 
(*exploring the consistency and models of the ontology*)
lemma "True" nitpick[satisfy,show_all,card i=1] oops
lemma "True" nitpick[satisfy,show_all,card i=10] oops
lemma "\<lfloor>(\<^bold>\<not>INDIFF d) \<^bold>\<and> (\<^bold>\<not>INDIFF p) \<^bold>\<and> (\<^bold>\<not>INCONS d) \<^bold>\<and> (\<^bold>\<not>INCONS p) \<^bold>\<and>
  d\<upharpoonleft>RELI \<^bold>\<and> p\<upharpoonleft>WILL\<rfloor>"  nitpick[satisfy,max_genuine=10,show_all] oops

(*useful shorthand notation for aggregated values*) 
abbreviation agg::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("_\<^bold>\<oplus>_") where "v\<^sub>1\<^bold>\<oplus>v\<^sub>2 \<equiv> v\<^sub>1 \<^bold>\<or> v\<^sub>2"
abbreviation Agg2 ("_\<upharpoonleft>[_\<oplus>_]") where "c\<upharpoonleft>[V1\<oplus>V2] \<equiv> c\<upharpoonleft>V1 \<^bold>\<oplus> c\<upharpoonleft>V2"
abbreviation Agg3 ("_\<upharpoonleft>[_\<oplus>_\<oplus>_]")
  where "c\<upharpoonleft>[V1\<oplus>V2\<oplus>V3] \<equiv> c\<upharpoonleft>V1 \<^bold>\<oplus> (c\<upharpoonleft>V2 \<^bold>\<oplus> c\<upharpoonleft>V3)"
abbreviation Agg4 ("_\<upharpoonleft>[_\<oplus>_\<oplus>_\<oplus>_]") 
  where "c\<upharpoonleft>[V1\<oplus>V2\<oplus>V3\<oplus>V4] \<equiv> c\<upharpoonleft>V1 \<^bold>\<oplus> (c\<upharpoonleft>V2 \<^bold>\<oplus> (c\<upharpoonleft>V3 \<^bold>\<oplus> c\<upharpoonleft>V4))"

(*exploring implied knowledge*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" 
  nitpick oops (*two non-opposed quadrants \<oplus> (noq): consistent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>GAIN\<oplus>EFFI\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" 
  nitpick oops (*two noq \<oplus>: consistent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>EFFI\<oplus>RELI] \<^bold>\<rightarrow> INCONS x\<rfloor>" nitpick (*TODO redefine INCONS appropriately to validate this*)
  by simp (*three quadrants \<oplus>: inconsistent*)
lemma "\<lfloor>x\<upharpoonleft>[RESP\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>"  nitpick (*TODO redefine INCONS appropriately to validate this*)
  by simp (*two opposed quadrants \<oplus> (oq): inconsistent*)
lemma "\<lfloor>x\<upharpoonleft>EQUI \<^bold>\<and> y\<upharpoonleft>EFFI \<^bold>\<rightarrow> (INCONS x \<^bold>\<or> INCONS y)\<rfloor>" 
  nitpick oops (*two noq (different parties): consistent*)
lemma "\<lfloor>x\<upharpoonleft>RESP \<^bold>\<and> y\<upharpoonleft>STAB \<^bold>\<rightarrow> (INCONS x \<^bold>\<or> INCONS y)\<rfloor>" 
  nitpick oops (*two oq (different parties): consistent*)

(*Important: only AE/EA preference variants are suitable for the
logic of value aggregation (aggregating values by union/disjunction)*)
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent --TODO: should also be countersatisfiable(?)*)
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>STAB\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>STAB\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>[RELI\<oplus>STAB]\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>STAB\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent --TODO: should also be countersatisfiable(?)*)
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>[RELI\<oplus>STAB]\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>STAB\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<^bold>\<prec> x\<upharpoonleft>WILL\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent --TODO: should also be satisfiable(?)*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<^bold>\<prec> x\<upharpoonleft>WILL\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>STAB \<^bold>\<prec> x\<upharpoonleft>WILL\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>[RELI\<oplus>STAB] \<^bold>\<prec> x\<upharpoonleft>WILL\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>STAB \<^bold>\<prec> x\<upharpoonleft>WILL\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>STAB \<^bold>\<prec> x\<upharpoonleft>WILL\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<^bold>\<prec> x\<upharpoonleft>WILL\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent --TODO: should also be countersatisfiable(?)*)
lemma "\<lfloor>x\<upharpoonleft>STAB \<^bold>\<prec> x\<upharpoonleft>WILL\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>[RELI\<oplus>STAB] \<^bold>\<prec> x\<upharpoonleft>WILL\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)

end

