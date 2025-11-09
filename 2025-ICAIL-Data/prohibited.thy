theory prohibited
  imports 
    DDL
   types
begin

consts (*Predicates/relations*)
  subliminal_technique::"aiSys\<Rightarrow>\<sigma>" (*deploys a subliminal technique beyond a persons consciousness*)
  has_consequence::"aiSys\<Rightarrow>consequence\<Rightarrow>\<sigma>" (*system has or may have a consequence*)
  has_purpose::"aiSys\<Rightarrow>purpose\<Rightarrow>\<sigma>" (*system has a purpose*)
  exploits_vulnerabilities_group::"aiSys\<Rightarrow>quality_person\<Rightarrow>\<sigma>" 
  exploits_vulnerable_group::"aiSys\<Rightarrow>\<sigma>" (*exploits any of the vulnerabilities of a specific group due to a certain quality*)
  employed_by_pauthorities::"aiSys\<Rightarrow>\<sigma>" (*employed by public authorities or on their behalf*)
  prohibited :: "aiSys \<Rightarrow> \<sigma>" (*placing on market, putting into service, or use*)

abbreviation "H1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. ((has_consequence x harm_physical) \<^bold>\<or> 
(has_consequence x harm_psychological)) \<^bold>\<leftrightarrow> has_consequence x harm\<rfloor>"
abbreviation "H2 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. ((exploits_vulnerabilities_group x age) \<^bold>\<or> (exploits_vulnerabilities_group x physcial_disability)
\<^bold>\<or> (exploits_vulnerabilities_group x mental_disability)) \<^bold>\<leftrightarrow> exploits_vulnerable_group x\<rfloor>" 
abbreviation "A1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. subliminal_technique x  \<^bold>\<and>  has_consequence x harm \<^bold>\<and> 
has_purpose x distort_behavior \<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>"
abbreviation "B1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. exploits_vulnerable_group x \<^bold>\<and> has_purpose x distort_behavior \<^bold>\<and> 
has_consequence x harm \<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>" 
abbreviation "C1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. employed_by_pauthorities x \<^bold>\<and> has_purpose x eval_trustworthiness_over_time \<^bold>\<and> 
(has_consequence x detri_treatment_unrelated_context \<^bold>\<or> has_consequence x detri_treatment_unjustified_disprop)
\<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>"

consts
  x::aiSys 

abbreviation "F1 w \<equiv> (subliminal_technique x) w"
abbreviation "F2 w \<equiv> (has_consequence x harm_physical) w"
abbreviation "F3 w \<equiv> (has_purpose x distort_behavior) w"


theorem Result1a: "H1 \<and> H2 \<and> A1 \<and> B1 \<and> C1 \<longrightarrow> \<lfloor>(F1 \<^bold>\<and> F2 \<^bold>\<and> F3)  \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited x>)\<rfloor>"  
  by metis

theorem Result1b: "H1 \<and> H2 \<and> A1 \<and> B1 \<and> C1 \<longrightarrow> \<lfloor>F1 \<^bold>\<and> F2  \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited x>)\<rfloor>"  
  nitpick [user_axioms] oops (*counterexample found*)

lemma True nitpick [satisfy, user_axioms, show_all] oops
