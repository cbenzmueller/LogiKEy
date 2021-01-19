theory PreferenceLogicBasics imports Main         (*** Benzmüller & Fuenmayor, 2021 ***)
begin (*unimportant*) declare[[syntax_ambiguity_warning=false]] 
      (*unimportant*) nitpick_params[user_axioms,expect=genuine,show_all,format=3]
(*** SSE of preference logic by van Benthem et al., JPL 2009 ***)
 (*preliminaries*)
typedecl \<iota>                  (*possible worlds*)      
type_synonym \<sigma>="\<iota>\<Rightarrow>bool"    (*'world-lifted' propositions*)
type_synonym \<gamma>="\<iota>\<Rightarrow>\<iota>\<Rightarrow>bool"  (*preference relations*)
type_synonym \<mu>="\<sigma>\<Rightarrow>\<sigma>"       (*unary logical connectives*)
type_synonym \<nu>="\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"    (*binary logical connectives*)
type_synonym \<pi>="\<sigma>\<Rightarrow>bool"    (*sets of world-lifted propositions*)
 (*betterness relation \<preceq> and strict betterness relation \<prec>*)
consts BR::\<gamma> ("_\<preceq>_") 
definition SBR::\<gamma> ("_\<prec>_") where "v\<prec>w \<equiv> (v\<preceq>w) \<and> \<not>(w\<preceq>v)" 
abbreviation "reflexive R \<equiv> \<forall>x. R x x"
abbreviation "transitive R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation "is_total R \<equiv> \<forall>x y. R x y \<or> R y x"
axiomatization where rBR: "reflexive BR" and tBR: "transitive BR"
lemma tSBR: "transitive SBR" using SBR_def tBR by blast (*derived from axioms*)
 (*modal logic connectives (operating on truth-sets)*)
abbreviation c1::\<sigma>  ("\<^bold>\<bottom>")   where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation c2::\<sigma>  ("\<^bold>\<top>")   where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation c3::\<mu>  ("\<^bold>\<not>_")  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w.\<not>(\<phi> w)"
abbreviation c4::\<nu>  (infixl"\<^bold>\<and>"85) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<and>(\<psi> w)"   
abbreviation c5::\<nu>  (infixl"\<^bold>\<or>"83) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<or>(\<psi> w)"
abbreviation c6::\<nu>  (infixl"\<^bold>\<rightarrow>"84) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longrightarrow>(\<psi> w)"  
abbreviation c7::\<nu>  (infixl"\<^bold>\<leftrightarrow>"84) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longleftrightarrow>(\<psi> w)"
abbreviation c8::\<mu>  ("\<^bold>\<box>\<^sup>\<preceq>_") where "\<^bold>\<box>\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<forall>v.(w\<preceq>v)\<longrightarrow>(\<phi> v)"
abbreviation c9::\<mu>  ("\<^bold>\<diamond>\<^sup>\<preceq>_") where "\<^bold>\<diamond>\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<exists>v.(w\<preceq>v)\<and>(\<phi> v)"
abbreviation c10::\<mu> ("\<^bold>\<box>\<^sup>\<prec>_") where "\<^bold>\<box>\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<forall>v.(w\<prec>v)\<longrightarrow>(\<phi> v)"
abbreviation c11::\<mu> ("\<^bold>\<diamond>\<^sup>\<prec>_") where "\<^bold>\<diamond>\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<exists>v.(w\<prec>v)\<and>(\<phi> v)"
abbreviation c12::\<mu> ("\<^bold>E_")  where "\<^bold>E\<phi> \<equiv> \<lambda>w.\<exists>v.(\<phi> v)" 
abbreviation c13::\<mu> ("\<^bold>A_")  where "\<^bold>A\<phi> \<equiv> \<lambda>w.\<forall>v.(\<phi> v)" 
 (*meta-logical predicate for global and validity*)
abbreviation g1::\<pi> ("\<lfloor>_\<rfloor>")  where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w. \<psi> w"
 (*some tests: dualities*)
lemma "\<lfloor>(\<^bold>\<diamond>\<^sup>\<preceq>\<phi>)\<^bold>\<leftrightarrow>(\<^bold>\<not>\<^bold>\<box>\<^sup>\<preceq>\<^bold>\<not>\<phi>)\<rfloor> \<and> \<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<phi>)\<^bold>\<leftrightarrow>(\<^bold>\<not>\<^bold>\<box>\<^sup>\<prec>\<^bold>\<not>\<phi>)\<rfloor> \<and> \<lfloor>(\<^bold>A\<phi>)\<^bold>\<leftrightarrow>(\<^bold>\<not>\<^bold>E\<^bold>\<not>\<phi>)\<rfloor>" by blast (*proof*)
(**** Section 3: A basic modal preference language ****)
 (*Definition 5*)
abbreviation pEE::\<nu>  ("_\<preceq>\<^sub>E\<^sub>E_") where "(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) u \<equiv> \<exists>s. \<phi> s \<and> (\<exists>t. \<psi> t \<and> s\<preceq>t)" 
abbreviation pEEs::\<nu> ("_\<prec>\<^sub>E\<^sub>E_") where "(\<phi> \<prec>\<^sub>E\<^sub>E \<psi>) u \<equiv> \<exists>s. \<phi> s \<and> (\<exists>t. \<psi> t \<and> s\<prec>t)" 
abbreviation pEA::\<nu>  ("_\<preceq>\<^sub>E\<^sub>A_") where "(\<phi> \<preceq>\<^sub>E\<^sub>A \<psi>) u \<equiv> \<exists>t. \<psi> t \<and> (\<forall>s. \<phi> s \<longrightarrow> s\<preceq>t)"
abbreviation pEAs::\<nu> ("_\<prec>\<^sub>E\<^sub>A_") where "(\<phi> \<prec>\<^sub>E\<^sub>A \<psi>) u \<equiv> \<exists>t. \<psi> t \<and> (\<forall>s. \<phi> s \<longrightarrow> s\<prec>t)"
abbreviation pAE::\<nu>  ("_\<preceq>\<^sub>A\<^sub>E_") where "(\<phi> \<preceq>\<^sub>A\<^sub>E \<psi>) u \<equiv> \<forall>s. \<phi> s\<longrightarrow>(\<exists>t. \<psi> t \<and> s\<preceq>t)" 
abbreviation pAEs::\<nu> ("_\<prec>\<^sub>A\<^sub>E_") where "(\<phi> \<prec>\<^sub>A\<^sub>E \<psi>) u \<equiv> \<forall>s. \<phi> s\<longrightarrow>(\<exists>t. \<psi> t \<and> s\<prec>t)"
abbreviation pAA::\<nu>  ("_\<preceq>\<^sub>A\<^sub>A_") where "(\<phi> \<preceq>\<^sub>A\<^sub>A \<psi>) u \<equiv> \<forall>s. \<phi> s\<longrightarrow>(\<forall>t. \<psi> t\<longrightarrow>s\<preceq>t)" 
abbreviation pAAs::\<nu> ("_\<prec>\<^sub>A\<^sub>A_") where "(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) u \<equiv> \<forall>s. \<phi> s\<longrightarrow>(\<forall>t. \<psi> t\<longrightarrow>s\<prec>t)" 
abbreviation PEE::\<nu>   ("_\<^bold>\<preceq>\<^sub>E\<^sub>E_") where "\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi> \<equiv> \<^bold>E(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>)"
abbreviation PEEs::\<nu>  ("_\<^bold>\<prec>\<^sub>E\<^sub>E_") where "\<phi> \<^bold>\<prec>\<^sub>E\<^sub>E \<psi> \<equiv> \<^bold>E(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<prec>\<psi>)" 
abbreviation PEA::\<nu>   ("_\<^bold>\<preceq>\<^sub>E\<^sub>A_") where "\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>A \<psi> \<equiv> \<^bold>E(\<psi> \<^bold>\<and> \<^bold>\<box>\<^sup>\<prec>\<^bold>\<not>\<phi>)" 
abbreviation PEAs::\<nu>  ("_\<^bold>\<prec>\<^sub>E\<^sub>A_") where "\<phi> \<^bold>\<prec>\<^sub>E\<^sub>A \<psi> \<equiv> \<^bold>E(\<psi> \<^bold>\<and> \<^bold>\<box>\<^sup>\<preceq>\<^bold>\<not>\<phi>)" 
abbreviation PAE::\<nu>   ("_\<^bold>\<preceq>\<^sub>A\<^sub>E_") where "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>)" 
abbreviation PAEs::\<nu>  ("_\<^bold>\<prec>\<^sub>A\<^sub>E_") where "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>\<prec>\<psi>)" 
abbreviation PAA::\<nu>   ("_\<^bold>\<preceq>\<^sub>A\<^sub>A_") where "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi> \<equiv> \<^bold>A(\<psi> \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<prec>\<^bold>\<not>\<phi>)" 
abbreviation PAAs::\<nu>  ("_\<^bold>\<prec>\<^sub>A\<^sub>A_") where "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi> \<equiv> \<^bold>A(\<psi> \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>\<^bold>\<not>\<phi>)" 
 (*quantification for objects of arbitrary type*)  
abbreviation mforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
abbreviation mforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation mexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
abbreviation mexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"
 (*polymorphic operators for sets of worlds/values*)
abbreviation subs   (infix "\<^bold>\<sqsubseteq>" 70)  where "A\<^bold>\<sqsubseteq>B \<equiv> \<forall>x. A x \<longrightarrow> B x"
abbreviation union  (infixr "\<^bold>\<squnion>" 70) where "A\<^bold>\<squnion>B \<equiv> \<lambda>x. A x \<or> B x"
abbreviation inters (infixr "\<^bold>\<sqinter>" 70) where "A\<^bold>\<sqinter>B \<equiv> \<lambda>x. A x \<and> B x"
 (*consistency confirmed (trivial: only abbreviations introduced)*)
lemma True nitpick[satisfy,user_axioms] oops (*satisfying model*)
end

