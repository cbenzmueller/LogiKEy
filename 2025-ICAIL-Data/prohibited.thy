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

consts
  real_time_bioid::"aiSys\<Rightarrow>\<sigma>" (*system is a real time bio identification system*)
  use_public_spaces::"aiSys\<Rightarrow>\<sigma>" (*system is planned to be used in public spaces*)
  use_law_enforcement::"aiSys\<Rightarrow>\<sigma>" (*system is used for law enforcement*)
  strictly_necessary_for::"aiSys\<Rightarrow>purpose\<Rightarrow>\<sigma>" (*use of system is strictly necessary for a purpose*)
  consider_consequence::"aiSys\<Rightarrow>consequence\<Rightarrow>\<sigma>" (*consider specific consequence of the use of a system*)
  consider_consequence_no_use::"aiSys\<Rightarrow>consequence\<Rightarrow>\<sigma>" (*consider specific consequence of not using the system*)
  consider_context::"aiSys\<Rightarrow>\<sigma>" (*consider the context in which the system is used*)
  complies_with_bioid_rules::"aiSys\<Rightarrow>\<sigma>" (*does system comply or not?*)

abbreviation "D1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and> 
(((has_purpose x targeted_search) \<^bold>\<and> (\<^bold>\<not>(strictly_necessary_for x targeted_search))) \<^bold>\<or>
((has_purpose x detection) \<^bold>\<and> (\<^bold>\<not>(strictly_necessary_for x detection))) \<^bold>\<or> ((has_purpose x prevention) \<^bold>\<and> 
(\<^bold>\<not>(strictly_necessary_for x prevention)))) \<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>"
(*implicit: not prohibited*)
abbreviation "D1b \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and> 
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or>
((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection)) \<^bold>\<or> ((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<circle><prohibited x>) \<^bold>\<and> (\<^bold>\<circle><high_risk x>))\<rfloor>"
abbreviation "A2a \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and> 
  (\<^bold>\<circle><high_risk x>) \<^bold>\<rightarrow> \<^bold>\<circle><consider_consequence_no_use x harm_psychological> \<^bold>\<and>
  \<^bold>\<circle><consider_consequence_no_use x harm_physical>\<rfloor>"
abbreviation "A2b \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and> 
  (\<^bold>\<circle><high_risk x>) \<^bold>\<rightarrow> \<^bold>\<circle><consider_consequence x affect_personal_rights> \<^bold>\<and> \<^bold>\<circle><consider_consequence x affect_personal_freedom>\<rfloor>" 
abbreviation "A2c \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and> 
  (\<^bold>\<circle><high_risk x>) \<^bold>\<rightarrow> \<^bold>\<circle><complies_with_bioid_rules x>\<rfloor>"

consts
  z::aiSys 

abbreviation "F4 w \<equiv> (real_time_bioid z) w"
abbreviation "F5 w \<equiv> (use_public_spaces z) w"
abbreviation "F6 w \<equiv> (use_law_enforcement z) w"
abbreviation "F7 w \<equiv> (has_purpose z targeted_search) w" 
abbreviation "F8 w \<equiv> \<not>(strictly_necessary_for z targeted_search) w"
abbreviation "F9 w \<equiv> (strictly_necessary_for z targeted_search) w" 

theorem Result2a: "D1 \<and> D1b \<and> A2a \<and> A2b \<and> A2c \<longrightarrow> \<lfloor>F4 \<^bold>\<and> F5 \<^bold>\<and> F6 \<^bold>\<and> F7 \<^bold>\<and> F8 \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited z>)\<rfloor>"
  by meson

theorem Result2b: "D1 \<and> D1b \<and> A2a \<and> A2b \<and> A2c \<longrightarrow> \<lfloor>F4 \<^bold>\<and> F5 \<^bold>\<and> F6 \<^bold>\<and> F7 \<^bold>\<and> F9 \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited z>)\<rfloor>"
  nitpick [user_axioms, card i = 2] oops (*found counterexample*) 

lemma True nitpick [satisfy, user_axioms, show_all] oops

end

