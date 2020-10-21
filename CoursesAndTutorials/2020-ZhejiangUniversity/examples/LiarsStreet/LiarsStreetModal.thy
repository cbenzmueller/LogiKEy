theory LiarsStreetModal       (*Christoph Benzmüller, 2020*)
  imports Main
begin          
(*unimportant*) nitpick_params [user_axioms,assms=true,format=2,box=false,show_all]
(*unimportant*) declare [[show_abbrevs=false]]

(*** NOTE: This is still a failing attempt to address "Says" ***)

(*Type declarations and type abbreviations*)
typedecl i (*Possible worlds*)  
type_synonym \<sigma> = "i\<Rightarrow>bool" (*World-lifted propositions*)
type_synonym \<tau> = "i\<Rightarrow>i\<Rightarrow>bool" (*Lifted predicates*)
type_synonym \<mu> = "\<sigma>\<Rightarrow>\<sigma>" (*Unary modal connectives*)
type_synonym \<nu> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (*Binary modal connectives*)


(***********************************************************************************
 ******************  Modal Logic Connectives ***************************************
 ***********************************************************************************)

(*Modal logic connectives (operating on truth-sets)*)
abbreviation MFalse::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation MTrue::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation MNeg::\<mu> ("\<^bold>\<not>_") where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w.\<not>(\<phi> w)"
abbreviation MOr::\<nu> ("_\<^bold>\<and>_") where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<and>(\<psi> w)"   
abbreviation MAnd::\<nu> ("_\<^bold>\<or>_") where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<or>(\<psi> w)"
abbreviation MImp::\<nu> ("_\<^bold>\<rightarrow>_") where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longrightarrow>(\<psi> w)"  
abbreviation MEquiv::\<nu> ("_\<^bold>\<leftrightarrow>_") where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longleftrightarrow>(\<psi> w)"

abbreviation MBox::"\<tau>\<Rightarrow>\<mu>" ("\<^bold>[_\<^bold>] _") where "\<^bold>[r\<^bold>] \<phi> \<equiv> \<lambda>w.\<forall>v.(r w v)\<longrightarrow>(\<phi> v)"
abbreviation MDia::"\<tau>\<Rightarrow>\<mu>" ("\<^bold><_\<^bold>> _") where "\<^bold><r\<^bold>> \<phi> \<equiv> \<lambda>w.\<exists>v.(r w v)\<and>(\<phi> v)"

(*Polymorphic possibilist quantification*)
abbreviation MAllPoss ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x.(\<Phi> x w)"
abbreviation MAllPossB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation MExPoss ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x.(\<Phi> x w)"   
abbreviation MExPossB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 


(*Meta-logical predicate for global validity*)
abbreviation MgValid::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w. \<psi> w"
(*Meta-logical predicate for local validity*)
consts cw::i
abbreviation MlValid::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>c\<^sub>w") where "\<lfloor>\<psi>\<rfloor>\<^sub>c\<^sub>w \<equiv>  \<psi> cw"

(*Consistency, Barcan and converse Barcan formula*)
lemma True nitpick[satisfy] oops  (*Model found by Nitpick*)
lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>[r\<^bold>](\<phi> x)) \<^bold>\<rightarrow> \<^bold>[r\<^bold>](\<^bold>\<forall>x. \<phi> x)\<rfloor>" by simp 
lemma "\<lfloor>(\<^bold>[r\<^bold>](\<^bold>\<forall>x.(\<phi> x))) \<^bold>\<rightarrow> \<^bold>\<forall>x.\<^bold>[r\<^bold>](\<phi> x)\<rfloor>" by simp


(***********************************************************************************
 ******************  Some Basic Types of our Ontology ******************************
 ***********************************************************************************)

(* There are some kids, could be many more *)
consts Nilda::\<tau> Carla::\<tau>
axiomatization where Different: "Carla \<noteq> Nilda"

(* There are some roads, could be many more *)
datatype Street = LiarsStreet | TruthtellersRoad  

(***********************************************************************************
 ******************  Controlled Natural Language Library ***************************
 ******************  Logic and Modalities ******************************************
 ***********************************************************************************)

(*** NL phrases: standard logical connectives; examples ***)
abbreviation And ("_ and _") where "X and Y \<equiv> X \<^bold>\<and> Y"
abbreviation Or ("_ or _") where "X or Y \<equiv> X \<^bold>\<or> Y"
abbreviation Not ("not _") where "not X \<equiv> \<^bold>\<not>X"
abbreviation If_then ("If _ then _") where "If X then Y \<equiv> X \<^bold>\<rightarrow> Y"

(*** NL phrases: modal connectives; examples ***)


(* We can introduce modal NL phrases *)
definition  Says::"\<tau>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("_ says _")  where "X says \<phi> \<equiv> \<^bold>[X\<^bold>] \<phi> "    
definition  Knows::"\<tau>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("_ knows _") where "X knows \<phi> \<equiv> \<^bold>[X\<^bold>] \<phi> "   

(* We can introduce some further derived modal NL phrases *)
definition Lies ("lies _") where "lies X \<equiv> \<^bold>\<forall>Y. If (X says Y) then not Y"
definition Says_the_truth ("says-the-truth _") 
  where "says-the-truth X \<equiv> \<^bold>\<forall>Y. If (X says Y) then Y" 

(* We add the above defintions to our "bag" called "Defs" — Unimportant *)
named_theorems Defs
declare Says_def [Defs] Knows_def [Defs] Lies_def [Defs] Says_the_truth_def [Defs] 


(***********************************************************************************
 ****************** Controlled Natural Language Library ****************************
 ****************** Domain specific concepts ***************************************
 ***********************************************************************************)

(* Uninterpreted predicate: Lives_in *)
consts Lives_in::"\<tau>\<Rightarrow>Street\<Rightarrow>\<sigma>" ("_ lives-in _") 

(* Further derived NL phrases that concern "Lives_in" *)
definition Lives_not_in ("_ lives-not-in _")
  where "X lives-not-in G \<equiv> not (X lives-in G)"
definition Neither_nor_live_in ("neither _ nor _ live-in _") 
  where "neither X nor Y live-in G \<equiv> (not (X lives-in G)) and (not (Y lives-in G))"
definition Both_live_in ("both _ and _ live-in _") 
  where "both X and Y live-in G \<equiv> (X lives-in G) and (Y lives-in G)"

(* We add the above defintions to our "bag" called "Defs" — Unimportant *)
declare Lives_not_in_def [Defs] Neither_nor_live_in_def [Defs] Both_live_in_def [Defs] 


(***********************************************************************************
 ****************** Example Queries ************************************************
 ***********************************************************************************)


axiomatization where
A1:  "\<lfloor>If (X lives-in LiarsStreet) then (lies X)\<rfloor>"  and
A2:  "\<lfloor>If (X lives-in TruthtellersRoad) then (says-the-truth X)\<rfloor>" 

lemma Question1:
  assumes
   "\<lfloor>Nilda says (Carla lives-in TruthtellersRoad)\<rfloor>\<^sub>c\<^sub>w" 
   "\<lfloor>Carla says (Nilda lives-in TruthtellersRoad)\<rfloor>\<^sub>c\<^sub>w"
 shows
   "\<lfloor>((Nilda lives-in S1) and (Carla lives-in S2))\<rfloor>\<^sub>c\<^sub>w"       
  nitpick[satisfy] 
  oops


(*** Do we run into Paradoxes with the modelling of modalities? ***)

consts It_holds_that_One_plus_One_Equals_Two::\<sigma> 
       It_holds_that_Fermats_last_Theorem_is_True::\<sigma>

lemma Question8:
  assumes
   "\<lfloor>It_holds_that_One_plus_One_Equals_Two\<rfloor>\<^sub>c\<^sub>w" 
   "\<lfloor>It_holds_that_Fermats_last_Theorem_is_True\<rfloor>\<^sub>c\<^sub>w" 
   "\<lfloor>Carla says It_holds_that_One_plus_One_Equals_Two\<rfloor>\<^sub>c\<^sub>w"
  shows
   "\<lfloor>Carla says It_holds_that_Fermats_last_Theorem_is_True\<rfloor>\<^sub>c\<^sub>w"  
  unfolding Defs
  sledgehammer [verbose]
  nitpick oops

lemma Question9:
  assumes
   "\<lfloor>It_holds_that_One_plus_One_Equals_Two\<rfloor>\<^sub>c\<^sub>w" 
   "\<lfloor>It_holds_that_Fermats_last_Theorem_is_True\<rfloor>\<^sub>c\<^sub>w" 
   "\<lfloor>Carla knows It_holds_that_One_plus_One_Equals_Two\<rfloor>\<^sub>c\<^sub>w"
  shows
   "\<lfloor>Carla knows It_holds_that_Fermats_last_Theorem_is_True\<rfloor>\<^sub>c\<^sub>w"  
  sledgehammer [verbose](assms)
  nitpick  oops


(*** But! As the remainder shows this is still not a proper modeling 
     of "Says" --- See literature on public announcement logic and our
     recent paper at the Dali workshop ***)

lemma Question2:
  assumes
   "\<lfloor>Nilda says (Carla lives-in LiarsStreet)\<rfloor>\<^sub>c\<^sub>w"  
   "\<lfloor>Carla says (neither Nilda nor Carla live-in LiarsStreet)\<rfloor>\<^sub>c\<^sub>w"
  shows
   "\<lfloor>((Nilda lives-in S1) and (Carla lives-in S2))\<rfloor>\<^sub>c\<^sub>w"              
  nitpick[satisfy] oops


lemma Question3:
  assumes
   "\<lfloor>Nilda says (Carla lives-in LiarsStreet)\<rfloor>\<^sub>c\<^sub>w" 
   "\<lfloor>Carla says (Carla lives-in LiarsStreet)\<rfloor>\<^sub>c\<^sub>w" 
 shows
   "\<lfloor>((Nilda lives-in S1) and (Carla lives-in S2))\<rfloor>\<^sub>c\<^sub>w"    
  nitpick[satisfy,show_all] oops

lemma Question4:
  assumes
   "\<lfloor>Nilda says (Nilda says (Nilda lives-in LiarsStreet))\<rfloor>\<^sub>c\<^sub>w" 
 shows
   "\<lfloor>(Nilda lives-in S1)\<rfloor>"    
  nitpick[satisfy,show_all] oops

lemma Question5:
  assumes
   "\<lfloor>Nilda says (Nilda says (Nilda lives-not-in LiarsStreet))\<rfloor>\<^sub>c\<^sub>w" 
 shows
   "\<lfloor>(Nilda lives-in S1)\<rfloor>\<^sub>c\<^sub>w"    
  nitpick[satisfy] oops

lemma Question6:
  assumes
   "\<lfloor>Nilda says (Nilda says ((Nilda lives-in LiarsStreet) and (Nilda lives-in TruthtellersRoad)))\<rfloor>" 
 shows
   "\<lfloor>(Nilda lives-in S1)\<rfloor>\<^sub>c\<^sub>w"    
  nitpick[satisfy] oops

lemma Question7:
  assumes
   "\<lfloor>Nilda says (Carla says ((Nilda lives-in LiarsStreet) and (Nilda lives-in TruthtellersRoad)))\<rfloor>\<^sub>c\<^sub>w" 
 shows
   "\<lfloor>((Nilda lives-in S1) and (Carla lives-in S2))\<rfloor>\<^sub>c\<^sub>w"    
  nitpick[satisfy] oops


end