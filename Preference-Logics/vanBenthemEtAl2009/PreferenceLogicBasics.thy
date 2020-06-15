theory PreferenceLogicBasics imports Main   (*** Benzmüller & Fuenmayor, 2020 ***)
begin (*SSE of preference logic by van Benthem, Girard and Roy, JPL 2009, in HOL*)
declare[[syntax_ambiguity_warning=false]]     (*unimportant declaration for tool*)
nitpick_params[user_axioms,expect=genuine,show_all,format=3] (*unimportant*)
   
(**** Embedding of "a basic modal preference language" in HOL ****)
(*Preliminaries*)
typedecl i  (*Possible Worlds*)      
type_synonym \<sigma>="i\<Rightarrow>bool" type_synonym \<gamma>="i\<Rightarrow>i\<Rightarrow>bool" (*propositions, pref. rels.*)
type_synonym \<mu>="\<sigma>\<Rightarrow>\<sigma>"    type_synonym \<nu>="\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"   (*unary & binary connectives*)
type_synonym \<pi>="\<sigma>\<Rightarrow>bool"                     (*sets of world-lifted propositions*)

consts BR::\<gamma> ("_\<preceq>_") (*betterness relation*)
abbreviation SBR::\<gamma> ("_\<prec>_") where "v\<prec>w \<equiv> (v\<preceq>w) \<and> \<not>(w\<preceq>v)" (*strict betterness*)
abbreviation "reflexive Rel \<equiv> \<forall>x. Rel x x"
abbreviation "transitive Rel \<equiv> \<forall>x y z. Rel x y \<and> Rel y z \<longrightarrow> Rel x z"
abbreviation "is_total Rel \<equiv> \<forall>x y. Rel x y \<or> Rel y x"
axiomatization where reflBR: "reflexive BR" and transBR: "transitive BR"

(*Modal logic connectives (operating on truth-sets)*)
abbreviation c01::\<sigma> ("\<^bold>\<bottom>")   where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation c02::\<sigma> ("\<^bold>\<top>")   where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation c03::\<mu> ("\<^bold>\<not>_")  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w.\<not>(\<phi> w)"
abbreviation c04::\<nu> (infixl"\<^bold>\<and>"85) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<and>(\<psi> w)"   
abbreviation c05::\<nu> (infixl"\<^bold>\<or>"83) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<or>(\<psi> w)"
abbreviation c06::\<nu> (infixl"\<^bold>\<rightarrow>"84) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longrightarrow>(\<psi> w)"  
abbreviation c07::\<nu> (infixl"\<^bold>\<leftrightarrow>"84) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longleftrightarrow>(\<psi> w)"
abbreviation c08::\<mu> ("\<^bold>\<box>\<^sup>\<preceq>_") where "\<^bold>\<box>\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<forall>v.(w\<preceq>v)\<longrightarrow>(\<phi> v)"
abbreviation c09::\<mu> ("\<^bold>\<diamond>\<^sup>\<preceq>_") where "\<^bold>\<diamond>\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<exists>v.(w\<preceq>v)\<and>(\<phi> v)"
abbreviation c10::\<mu> ("\<^bold>\<box>\<^sup>\<prec>_") where "\<^bold>\<box>\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<forall>v.(w\<prec>v)\<longrightarrow>(\<phi> v)"
abbreviation c11::\<mu> ("\<^bold>\<diamond>\<^sup>\<prec>_") where "\<^bold>\<diamond>\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<exists>v.(w\<prec>v)\<and>(\<phi> v)"
abbreviation c12::\<mu> ("\<^bold>E_") where "\<^bold>E\<phi> \<equiv> \<lambda>w.\<exists>v.(\<phi> v)" (*Global existence modality*)
abbreviation c13::\<mu> ("\<^bold>A_") where "\<^bold>A\<phi> \<equiv> \<lambda>w.\<forall>v.(\<phi> v)" (*Global universal modality*)
(*Meta-logical predicate for global and validity*)
abbreviation g1::\<pi> ("\<lfloor>_\<rfloor>")   where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w. \<psi> w"

(*Some tests: dualities*)
lemma "\<lfloor>(\<^bold>\<diamond>\<^sup>\<preceq>\<phi>) \<^bold>\<leftrightarrow> (\<^bold>\<not>\<^bold>\<box>\<^sup>\<preceq>\<^bold>\<not>\<phi>)\<rfloor> \<and> \<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<leftrightarrow> (\<^bold>\<not>\<^bold>\<box>\<^sup>\<prec>\<^bold>\<not>\<phi>)\<rfloor> \<and> \<lfloor>(\<^bold>A\<phi>) \<^bold>\<leftrightarrow> (\<^bold>\<not>\<^bold>E\<^bold>\<not>\<phi>)\<rfloor>" by blast

(**** Section 3: A basic modal preference language ****)
(*Definition 5*)
abbreviation leqEE::\<nu>  ("_\<preceq>\<^sub>E\<^sub>E_") where  "(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) u \<equiv> \<exists>s.\<exists>t. \<phi> s \<and> \<psi> t \<and> s\<preceq>t" 
abbreviation leqAE::\<nu>  ("_\<preceq>\<^sub>A\<^sub>E_") where  "(\<phi> \<preceq>\<^sub>A\<^sub>E \<psi>) u \<equiv> \<forall>s.\<exists>t. \<phi> s \<longrightarrow> \<psi> t \<and> s\<preceq>t" 
abbreviation leEE::\<nu>   ("_\<prec>\<^sub>E\<^sub>E_") where  "(\<phi> \<prec>\<^sub>E\<^sub>E \<psi>) u \<equiv> \<exists>s.\<exists>t. \<phi> s \<and> \<psi> t \<and> s\<prec>t" 
abbreviation leAE::\<nu>   ("_\<prec>\<^sub>A\<^sub>E_") where  "(\<phi> \<prec>\<^sub>A\<^sub>E \<psi>) u \<equiv> \<forall>s.\<exists>t. \<phi> s \<longrightarrow> \<psi> t \<and> s\<prec>t" 
abbreviation leAA::\<nu>   ("_\<prec>\<^sub>A\<^sub>A_") where  "(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) u \<equiv> \<forall>s.\<forall>t. \<phi> s \<and> \<psi> t \<longrightarrow> s\<prec>t" 
abbreviation gEA::\<nu>    ("_\<succ>\<^sub>E\<^sub>A_") where  "(\<phi> \<succ>\<^sub>E\<^sub>A \<psi>) u \<equiv> \<exists>s.\<forall>t. \<phi> s \<and> \<psi> t \<longrightarrow> t\<prec>s" 
abbreviation leqAA::\<nu>  ("_\<preceq>\<^sub>A\<^sub>A_") where  "(\<phi> \<preceq>\<^sub>A\<^sub>A \<psi>) u \<equiv> \<forall>s.\<forall>t. \<phi> s \<and> \<psi> t \<longrightarrow> s\<preceq>t" 
abbreviation geqEA::\<nu>  ("_\<succeq>\<^sub>E\<^sub>A_") where  "(\<phi> \<succeq>\<^sub>E\<^sub>A \<psi>) u \<equiv> \<exists>s.\<forall>t. \<phi> s \<and> \<psi> t \<longrightarrow> t\<preceq>s" 
abbreviation leqEE'::\<nu> ("_\<^bold>\<preceq>\<^sub>E\<^sub>E_") where  "\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi> \<equiv> \<^bold>E(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>)"
abbreviation leqAE'::\<nu> ("_\<^bold>\<preceq>\<^sub>A\<^sub>E_") where  "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>)" 
abbreviation leEE'::\<nu>  ("_\<^bold>\<prec>\<^sub>E\<^sub>E_") where  "\<phi> \<^bold>\<prec>\<^sub>E\<^sub>E \<psi> \<equiv> \<^bold>E(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<prec>\<psi>)" 
abbreviation leAA'::\<nu>  ("_\<^bold>\<prec>\<^sub>A\<^sub>A_") where  "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi> \<equiv> \<^bold>A(\<psi> \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>\<^bold>\<not>\<phi>)" 
abbreviation gEA'::\<nu>   ("_\<^bold>\<succ>\<^sub>E\<^sub>A_") where  "\<phi> \<^bold>\<succ>\<^sub>E\<^sub>A \<psi> \<equiv> \<^bold>E(\<phi> \<^bold>\<and> \<^bold>\<box>\<^sup>\<preceq>\<^bold>\<not>\<psi>)" 
abbreviation leqAA'::\<nu> ("_\<^bold>\<preceq>\<^sub>A\<^sub>A_") where  "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<and> \<^bold>\<box>\<^sup>\<prec>\<^bold>\<not>\<psi>)" 
abbreviation geqEA'::\<nu> ("_\<^bold>\<succeq>\<^sub>E\<^sub>A_") where  "\<phi> \<^bold>\<succeq>\<^sub>E\<^sub>A \<psi> \<equiv> \<^bold>E(\<phi> \<^bold>\<and> \<^bold>\<box>\<^sup>\<prec>\<^bold>\<not>\<psi>)" 
abbreviation leAE'::\<nu>  ("_\<^bold>\<prec>\<^sub>A\<^sub>E_") where  "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>\<prec>\<psi>)" 

(* quantification for objects of arbitrary type.*)  
abbreviation mforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
abbreviation mforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation mexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
abbreviation mexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"

(*Consistency confirmed by nitpick (trivial: only abbreviations are introduced)*)
lemma True nitpick[satisfy,user_axioms] oops
end

