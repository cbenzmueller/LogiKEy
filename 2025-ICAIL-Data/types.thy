theory types     
  imports Main 
begin

(*SDL types*)
typedecl i (*Type for possible worlds.*) 
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<gamma> = "\<sigma>\<Rightarrow>\<sigma>" 
type_synonym \<rho> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
(*SDL_agents/ Dstit_Deontic types*)
typedecl ag (*Type for agents*)
type_synonym \<tau> = "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" 
type_synonym \<kappa> = "(ag\<Rightarrow>i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" 

type_synonym \<nu> = "(\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool))\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<mu> = "(\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool))\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<zeta> = "(i\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"

type_synonym \<delta> = "i\<Rightarrow>i\<Rightarrow>bool" (* type of accessibility relations between worlds Dstit_Deontic*)

(*Other types needed for tiles & articles*)
(*prohibited*)
typedecl aiSys (*Type for AI-systems*)
datatype quality_person = age | physcial_disability | mental_disability (*quality of a person*)
datatype consequence = harm | harm_physical | harm_psychological | detri_treatment_unrelated_context | 
detri_treatment_unjustified_disprop | affect_personal_rights | affect_personal_freedom (*type for consequences caused by AI-systems*)
datatype purpose = distort_behavior | exploit_groups | eval_trustworthiness_over_time | targeted_search | 
prevention | detection (*type for purposes of AI-systems*)

consts
   prohibited::"aiSys\<Rightarrow>\<sigma>" (*system is declared prohibited*)
   high_risk::"aiSys\<Rightarrow>\<sigma>" (*system is declared a high-risk system*)

typedecl national_law  (*national law of member states*) 

(*high-risk-3-1-6-7*)
(*degree of a quality, strength*)
datatype degree = low | medium | high

(*high-risk-3-2-8-9*)
typedecl rms (*risk-management-system*)
typedecl soa (*state of art*)
datatype risk = data_leak | incorrect_info | discrimination (*risks posed by an AI system*)
(*high-risk-3-2-10*)
typedecl tvt_dsets (*training, validation, testing data sets*)
typedecl data (*generic data*)
typedecl gov_and_man_practices (*appropriate governance and management practices*)
typedecl particularities (*specific geographical, behavioural or functional setting within which the 
high-risk AI system is intended to be used*)
typedecl devproc (*development process Art10, point 6*)

(*high-risk-3-3-27*)
typedecl stor_tra_conditions (*storage or transport conditions*)

(*high-risk-3-4-31*)
typedecl appl_nb (*application for notification*)

(*high-risk-3-5-44*)
typedecl certificate (*certificate by notified body*)

(*chapter3_17*)
typedecl qualManSys (*quality management system*)
datatype standard = harm_stand_art_40 (*standards that must be considered*)
datatype size = small | medium | large (*size of provider's organisation*)

(*Article 32: mult_AgTests*)
typedecl notification (*notification of a conformity assessment body*)

consts
    (*identify agents:*)
    a::ag (*a = type for judicial authorities or independent administrative authorities*)
    b::ag (*b = type for importers*)   
    c::ag (*c = type for eu commission*)
    d::ag (*d = type for providers*)
    e::ag (*e = type for conformity assessment bodies*)
    f::ag (*f = type for notifying authorities*)
    g::ag (*g = type for notified bodies*)
    h::ag (*h = type for members states*)

end