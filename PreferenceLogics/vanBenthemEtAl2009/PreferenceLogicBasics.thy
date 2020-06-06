theory PreferenceLogicBasics imports Main              
begin 
(*some conceptually unimportant declarations of defaults for tools*) 
   nitpick_params[assms=true,user_axioms=true,expect=genuine,format=3] 
   declare [["syntax_ambiguity_warning" = false]]

(**** Embedding of "a basic modal preference language" in HOL  ****)
typedecl i (*Possible worlds*)  
typedecl e (*Individuals*)      
type_synonym \<sigma> = "i\<Rightarrow>bool" (*World-lifted propositions*)
type_synonym \<mu> = "\<sigma>\<Rightarrow>\<sigma>" (*Unary modal connectives*)
type_synonym \<nu> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (*Binary modal connectives*)
type_synonym \<gamma> = "i\<Rightarrow>i\<Rightarrow>bool" (*Preference relations*)
type_synonym \<pi> = "\<sigma>\<Rightarrow>bool" (*Sets of world-lifted propositions*)

consts BR::\<gamma> ("_\<preceq>_")  (*Betterness relation*)
abbreviation SBR::\<gamma> ("_\<prec>_")  where  "v\<prec>w \<equiv> (v\<preceq>w) \<and> \<not>(w\<preceq>v)" (*Strict Betterness relation*)

abbreviation reflexive :: "\<gamma>\<Rightarrow>bool" where "reflexive Rel \<equiv> \<forall>x. Rel x x"
abbreviation transitive :: "\<gamma>\<Rightarrow>bool" where "transitive Rel \<equiv> \<forall>x y z. Rel x y \<and> Rel y z \<longrightarrow> Rel x z"
abbreviation total :: "\<gamma>\<Rightarrow>bool" where "total Rel \<equiv> \<forall>x y. Rel x y \<or> Rel y x"
abbreviation irreflexive :: "\<gamma>\<Rightarrow>bool" where "irreflexive Rel \<equiv> \<forall>x. \<not>(Rel x x)"

axiomatization where     reflBR: "reflexive BR"      and     transBR: "transitive BR"

lemma "irreflexive SBR \<and> transitive SBR" using transBR by blast
lemma "total SBR \<longrightarrow> total BR" by auto

(*Modal logic connectives (operating on truth-sets)*)
abbreviation c1::\<sigma>  ("\<^bold>\<bottom>")     where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation c2::\<sigma>  ("\<^bold>\<top>")     where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation c3::\<mu>  ("\<^bold>\<not>_")    where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w.\<not>(\<phi> w)"
abbreviation c4::\<nu>   ("_\<^bold>\<and>_")  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<and>(\<psi> w)"   
abbreviation c5::\<nu>   ("_\<^bold>\<or>_")  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<or>(\<psi> w)"
abbreviation c6::\<nu>   ("_\<^bold>\<rightarrow>_") where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longrightarrow>(\<psi> w)"  
abbreviation c7::\<nu>   ("_\<^bold>\<leftrightarrow>_") where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longleftrightarrow>(\<psi> w)"
abbreviation c8::\<mu>   ("\<^bold>\<box>\<^sup>\<preceq>_") where "\<^bold>\<box>\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<forall>v.(w\<preceq>v)\<longrightarrow>(\<phi> v)"
abbreviation c9::\<mu>   ("\<^bold>\<diamond>\<^sup>\<preceq>_") where "\<^bold>\<diamond>\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<exists>v.(w\<preceq>v)\<and>(\<phi> v)"
abbreviation c10::\<mu> ("\<^bold>\<box>\<^sup>\<prec>_") where "\<^bold>\<box>\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<forall>v.(w\<prec>v)\<longrightarrow>(\<phi> v)"
abbreviation c11::\<mu> ("\<^bold>\<diamond>\<^sup>\<prec>_") where "\<^bold>\<diamond>\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<exists>v.(w\<prec>v)\<and>(\<phi> v)"
abbreviation c12::\<mu> ("\<^bold>E_")    where "\<^bold>E\<phi> \<equiv> \<lambda>w.\<exists>v.(\<phi> v)"  (*Global existence modality*)
abbreviation c13::\<mu> ("\<^bold>A_")    where "\<^bold>A\<phi> \<equiv> \<lambda>w.\<forall>v.(\<phi> v)"  (*Global universal modality*)
(*Meta-logical predicate for global validity*)
abbreviation g1::\<pi> ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w. \<psi> w"

(*Some tests: dualities*)
lemma "\<lfloor>(\<^bold>\<diamond>\<^sup>\<preceq>\<phi>) \<^bold>\<leftrightarrow> (\<^bold>\<not>\<^bold>\<box>\<^sup>\<preceq>\<^bold>\<not>\<phi>)\<rfloor>" by blast
lemma "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<leftrightarrow> (\<^bold>\<not>\<^bold>\<box>\<^sup>\<prec>\<^bold>\<not>\<phi>)\<rfloor>" by blast
lemma "\<lfloor>(\<^bold>A\<phi>) \<^bold>\<leftrightarrow> (\<^bold>\<not>\<^bold>E\<^bold>\<not>\<phi>)\<rfloor>" by blast

(**** Section 3: A basic modal preference language ****)
(*Definition 5*)
abbreviation leqEE::\<nu>  ("_\<preceq>\<^sub>E\<^sub>E_")  where  "(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) u \<equiv> \<exists>s. \<exists>t. (\<phi> s) \<and> (\<psi> t) \<and> (s\<preceq>t)" 
abbreviation leqAE::\<nu>  ("_\<preceq>\<^sub>A\<^sub>E_")  where  "(\<phi> \<preceq>\<^sub>A\<^sub>E \<psi>) u \<equiv> \<forall>s. \<exists>t. (\<phi> s) \<longrightarrow> (\<psi> t) \<and> (s\<preceq>t)" 
abbreviation leEE::\<nu>    ("_\<prec>\<^sub>E\<^sub>E_")  where  "(\<phi> \<prec>\<^sub>E\<^sub>E \<psi>) u \<equiv> \<exists>s. \<exists>t. (\<phi> s) \<and> (\<psi> t) \<and> (s\<prec>t)" 
abbreviation leAE::\<nu>    ("_\<prec>\<^sub>A\<^sub>E_")  where  "(\<phi> \<prec>\<^sub>A\<^sub>E \<psi>) u \<equiv> \<forall>s. \<exists>t. (\<phi> s) \<longrightarrow> (\<psi> t) \<and> (s\<prec>t)" 
abbreviation leAA::\<nu>    ("_\<prec>\<^sub>A\<^sub>A_")  where  "(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) u \<equiv> \<forall>s. \<forall>t. (\<phi> s) \<and> (\<psi> t) \<longrightarrow> (s\<prec>t)" 
abbreviation gEA::\<nu>     ("_\<succ>\<^sub>E\<^sub>A_")  where  "(\<phi> \<succ>\<^sub>E\<^sub>A \<psi>) u \<equiv> \<exists>s. \<forall>t. (\<phi> s) \<and> (\<psi> t) \<longrightarrow> (t\<prec>s)" 
abbreviation leqAA::\<nu>  ("_\<preceq>\<^sub>A\<^sub>A_")  where  "(\<phi> \<preceq>\<^sub>A\<^sub>A \<psi>) u \<equiv> \<forall>s. \<forall>t. (\<phi> s) \<and> (\<psi> t) \<longrightarrow> (s\<preceq>t)" 
abbreviation geqEA::\<nu> ("_\<succeq>\<^sub>E\<^sub>A_")  where  "(\<phi> \<succeq>\<^sub>E\<^sub>A \<psi>) u \<equiv> \<exists>s. \<forall>t. (\<phi> s) \<and> (\<psi> t) \<longrightarrow> (t\<preceq>s)" 
abbreviation leqEE'::\<nu>  ("_\<^bold>\<preceq>\<^sub>E\<^sub>E_")  where  "\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi> \<equiv> \<^bold>E(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>)"
abbreviation leqAE'::\<nu>  ("_\<^bold>\<preceq>\<^sub>A\<^sub>E_")  where  "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>)" 
abbreviation leEE'::\<nu>    ("_\<^bold>\<prec>\<^sub>E\<^sub>E_")  where  "\<phi> \<^bold>\<prec>\<^sub>E\<^sub>E \<psi> \<equiv> \<^bold>E(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<prec>\<psi>)" 
abbreviation leAA'::\<nu>    ("_\<^bold>\<prec>\<^sub>A\<^sub>A_")  where  "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi> \<equiv> \<^bold>A(\<psi> \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>\<^bold>\<not>\<phi>)" 
abbreviation gEA'::\<nu>     ("_\<^bold>\<succ>\<^sub>E\<^sub>A_")  where  "\<phi> \<^bold>\<succ>\<^sub>E\<^sub>A \<psi> \<equiv> \<^bold>E(\<phi> \<^bold>\<and> \<^bold>\<box>\<^sup>\<preceq>\<^bold>\<not>\<psi>)" 
abbreviation leqAA'::\<nu>  ("_\<^bold>\<preceq>\<^sub>A\<^sub>A_")  where  "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<and> \<^bold>\<box>\<^sup>\<prec>\<^bold>\<not>\<psi>)" 
abbreviation geqEA'::\<nu> ("_\<^bold>\<succeq>\<^sub>E\<^sub>A_")  where  "\<phi> \<^bold>\<succeq>\<^sub>E\<^sub>A \<psi> \<equiv> \<^bold>E(\<phi> \<^bold>\<and> \<^bold>\<box>\<^sup>\<prec>\<^bold>\<not>\<psi>)" 
abbreviation leAE'::\<nu>    ("_\<^bold>\<prec>\<^sub>A\<^sub>E_")  where  "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>\<prec>\<psi>)" 

(**** Section 5: Equality-based Ceteris Paribus Preference Logic ****)
abbreviation elem::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>bool" ("_\<^bold>\<in>_")  where  "\<phi> \<^bold>\<in> \<Gamma> \<equiv> \<Gamma> \<phi>" 
abbreviation subseteq::"\<pi>\<Rightarrow>\<pi>\<Rightarrow>bool" ("_\<^bold>\<subseteq>_")  where  "\<Gamma> \<^bold>\<subseteq> \<Gamma>' \<equiv> \<forall>\<phi>. (\<phi> \<^bold>\<in> \<Gamma>) \<longrightarrow> (\<phi> \<^bold>\<in> \<Gamma>')" 
abbreviation union::"\<pi>\<Rightarrow>\<pi>\<Rightarrow>\<pi>" ("_\<^bold>\<union>_")  where  "\<Gamma> \<^bold>\<union> \<Gamma>' \<equiv> \<lambda>\<phi>. (\<phi> \<^bold>\<in> \<Gamma>) \<or> (\<phi> \<^bold>\<in> \<Gamma>')" 
abbreviation intersec::"\<pi>\<Rightarrow>\<pi>\<Rightarrow>\<pi>" ("_\<^bold>\<inter>_")  where  "\<Gamma> \<^bold>\<inter> \<Gamma>' \<equiv> \<lambda>\<phi>. (\<phi> \<^bold>\<in> \<Gamma>) \<and> (\<phi> \<^bold>\<in> \<Gamma>')" 
abbreviation mkSet1::"\<sigma>\<Rightarrow>\<pi>" ("\<^bold>{_\<^bold>}")  where  "\<^bold>{\<phi>\<^bold>} \<equiv> \<lambda>x. x=\<phi>" 
abbreviation mkSet2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<pi>" ("\<^bold>{_,_\<^bold>}")  where  "\<^bold>{\<alpha>,\<beta>\<^bold>} \<equiv> \<lambda>x. x=\<alpha> \<or> x=\<beta>" 
abbreviation mkSet3::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<pi>" ("\<^bold>{_,_,_\<^bold>}")  where  "\<^bold>{\<alpha>,\<beta>,\<gamma>\<^bold>} \<equiv> \<lambda>x. x=\<alpha> \<or> x=\<beta> \<or> x=\<gamma>" 
abbreviation emptySet ("\<^bold>\<emptyset>") where "\<^bold>\<emptyset> \<equiv> (\<lambda> \<psi>. False)"
abbreviation univSet ("\<^bold>\<U>") where "\<^bold>\<U> \<equiv> (\<lambda> \<psi>. True)"

abbreviation c14::"i\<Rightarrow>\<pi>\<Rightarrow>i\<Rightarrow>bool" ("_ \<^bold>\<equiv>\<^sub>_ _") where "w \<^bold>\<equiv>\<^sub>\<Gamma> v \<equiv> \<forall>\<phi>. (\<phi> \<^bold>\<in> \<Gamma>) \<longrightarrow> ((\<phi> w) \<longleftrightarrow> (\<phi> v))"
abbreviation c15::"i\<Rightarrow>\<pi>\<Rightarrow>i\<Rightarrow>bool" ("_ \<^bold>\<unlhd>\<^sub>_ _") where "w \<^bold>\<unlhd>\<^sub>\<Gamma> v \<equiv>  (w \<preceq> v) \<and> (w \<^bold>\<equiv>\<^sub>\<Gamma> v)"
abbreviation c16::"i\<Rightarrow>\<pi>\<Rightarrow>i\<Rightarrow>bool" ("_ \<^bold>\<lhd>\<^sub>_ _") where "w \<^bold>\<lhd>\<^sub>\<Gamma> v \<equiv>  (w \<prec> v) \<and> (w \<^bold>\<equiv>\<^sub>\<Gamma> v)"
abbreviation c17::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<langle>_\<^bold>\<rangle>\<^sup>\<preceq>_") where "\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<exists>v. (w \<^bold>\<unlhd>\<^sub>\<Gamma> v) \<and> (\<phi> v)"
abbreviation c18::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("[_]\<^sup>\<preceq>_") where "[\<Gamma>]\<^sup>\<preceq>\<phi> \<equiv> \<lambda>w.\<forall>v. (w \<^bold>\<unlhd>\<^sub>\<Gamma> v) \<longrightarrow> (\<phi> v)"
abbreviation c19::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<langle>_\<^bold>\<rangle>\<^sup>\<prec>_") where "\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<exists>v. (w \<^bold>\<lhd>\<^sub>\<Gamma> v) \<and> (\<phi> v)"
abbreviation c20::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("[_]\<^sup>\<prec>_") where "[\<Gamma>]\<^sup>\<prec>\<phi> \<equiv> \<lambda>w.\<forall>v. (w \<^bold>\<lhd>\<^sub>\<Gamma> v) \<longrightarrow> (\<phi> v)"
abbreviation c21::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<langle>_\<^bold>\<rangle>_") where "\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi> \<equiv> \<lambda>w.\<exists>v. (w \<^bold>\<equiv>\<^sub>\<Gamma> v) \<and> (\<phi> v)"
abbreviation c22::"\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("[_]_") where "[\<Gamma>]\<phi> \<equiv> \<lambda>w.\<forall>v. (w \<^bold>\<equiv>\<^sub>\<Gamma> v) \<longrightarrow> (\<phi> v)"

(**** Section 6: Ceteris Paribus Counterparts of Binary Preference Statements ****)
(*Note: the operators below are not defined in the paper (their existence is tacitly suggested).
Only the operator \<prec>\<^sup>\<Gamma> is defined in the paper, it aims at modelling von Wright's notion of
ceteris paribus ("all other things being equal") preferences (w.r.t. a set of formulas \<Gamma>).
That variant corresponds to \<prec>\<^sub>A\<^sub>A\<^sup>\<Sigma> below, where \<Sigma>=cp(\<Gamma>), i.e., \<Sigma> are the propositional atoms
independent from (not occurring in) \<Gamma>, they are to be elicited by extra-logical means.
Our variants below can thus be understood as "these (given) things being equal"-preferences. *)

(*AA-variant (drawing upon von Wright's)*)
abbreviation leAA_cp::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("_\<prec>\<^sub>A\<^sub>A\<^sup>_ _")  where  "(\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s. \<forall>t. (\<phi> s) \<and> (\<psi> t) \<longrightarrow> (s \<^bold>\<lhd>\<^sub>\<Gamma> t)"
abbreviation leAA_cp'::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("_\<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>_ _")  where  "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<psi> \<^bold>\<rightarrow> [\<Gamma>]\<^sup>\<preceq>\<^bold>\<not>\<phi>)" 
abbreviation leqAA_cp::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"   ("_\<preceq>\<^sub>A\<^sub>A\<^sup>_ _")  where  "(\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s. \<forall>t. (\<phi> s) \<and> (\<psi> t) \<longrightarrow> (s \<^bold>\<unlhd>\<^sub>\<Gamma> t)" 
abbreviation leqAA_cp'::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("_\<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>_ _")  where  "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<and> [\<Gamma>]\<^sup>\<prec>\<^bold>\<not>\<psi>)"

(*AE-variant *)
abbreviation leAE_cp::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("_\<prec>\<^sub>A\<^sub>E\<^sup>_ _") where "(\<phi> \<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s. \<exists>t. (\<phi> s) \<longrightarrow> (\<psi> t) \<and> (s \<^bold>\<lhd>\<^sub>\<Gamma> t)" 
abbreviation leAE_cp'::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("_\<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>_ _")  where  "\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<psi>)" 
abbreviation leqAE_cp::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("_\<preceq>\<^sub>A\<^sub>E\<^sup>_ _") where "(\<phi> \<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u \<equiv> \<forall>s. \<exists>t. (\<phi> s) \<longrightarrow> (\<psi> t) \<and> (s \<^bold>\<unlhd>\<^sub>\<Gamma> t)" 
abbreviation leqAE_cp'::"\<sigma>\<Rightarrow>\<pi>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("_\<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>_ _") where "\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi> \<equiv> \<^bold>A(\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<psi>)"

(*Consistency confirmed by nitpick (trivial since only abbreviations were introduced)*)
lemma True nitpick[satisfy,user_axioms] oops
end


