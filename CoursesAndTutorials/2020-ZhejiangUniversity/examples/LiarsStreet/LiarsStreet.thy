theory LiarsStreet imports  Main  (*Christoph Benzmüller, 2020*)
begin          
(*unimportant*) nitpick_params [user_axioms,format=2,show_all]
(*unimportant*) declare [[show_abbrevs=false]]

(***********************************************************************************
 ******************  Some Basic Types of our Ontology ******************************
 ***********************************************************************************)

(* There are some kids, could be many more *)
datatype Entity = Nilda | Carla  

(* There are some roads, could be many more *)
datatype Street = LiarsStreet | TruthtellersRoad  

(***********************************************************************************
 ******************  Controlled Natural Language Library ***************************
 ******************  Logic and Modalities ******************************************
 ***********************************************************************************)

definition And ("_ and _") where "X and Y \<equiv> X \<and> Y"
abbreviation Or ("_ or _") where "X or Y \<equiv> X \<or> Y"
definition Not ("not _") where "not X \<equiv> \<not>X"
definition If_then ("If _ then _") where "If X then Y \<equiv> X \<longrightarrow> Y"


(* "Says" "Knows" "Belief" "Obligation", etc. as uninterpreted truth-functions
   --- which, of course, will lead to known paradoxes *)
consts  Says::"Entity\<Rightarrow>bool\<Rightarrow>bool"  ("_ says _") 
consts  Knows::"Entity\<Rightarrow>bool\<Rightarrow>bool"  ("_ knows _")  
consts  Believes::"Entity\<Rightarrow>bool\<Rightarrow>bool"  ("_ believes _")    
consts  Obligation::"Entity\<Rightarrow>bool\<Rightarrow>bool"  ("_ must-do _") 

(* We can introduce some further derived modal NL phrases *)
definition Lies ("lies _") where "lies X \<equiv> \<forall>Y. If (X says Y) then not Y"
definition Says_the_truth ("says-the-truth _") 
  where "says-the-truth X \<equiv> \<forall>Y. If (X says Y) then Y" 

(* We add the above defintions to our "bag" called "Defs" — Unimportant *)
named_theorems Defs
declare Lies_def [Defs] Says_the_truth_def [Defs] 


(***********************************************************************************
 ****************** Controlled Natural Language Library ****************************
 ****************** Domain specific concepts ***************************************
 ***********************************************************************************)

(* Uninterpreted predicate: Lives_in *)
consts Lives_in::"Entity\<Rightarrow>Street\<Rightarrow>bool" ("_ lives-in _") 

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
A1:  "\<forall>X. If (X lives-in LiarsStreet) then (lies X)"  and
A2:  "\<forall>X. If (X lives-in TruthtellersRoad) then (says-the-truth X)" 


lemma Question1:
  assumes
   "Nilda says (Carla lives-in TruthtellersRoad)" 
   "Carla says (Nilda lives-in TruthtellersRoad)"
  shows
   "((Nilda lives-in S1) and (Carla lives-in S2))"         
  nitpick[satisfy] oops 


lemma Question1b:
  assumes
   "Nilda says (Carla lives-in TruthtellersRoad)" 
   "Carla says (Nilda lives-in TruthtellersRoad)"
  shows
   "((Nilda lives-in LiarsStreet) and (Carla lives-in S2))"         
  nitpick[satisfy] oops 

lemma Question2:
  assumes
   "Nilda says (Carla lives-in LiarsStreet)"  
   "Carla says (neither Nilda nor Carla live-in LiarsStreet)"
  shows
   "((Nilda lives-in S1) and (Carla lives-in S2))"         
  nitpick[satisfy] oops


lemma Question3:
  assumes
   "Nilda says (Carla lives-in LiarsStreet)" 
   "Carla says (Carla lives-in LiarsStreet)" 
 shows
   "((Nilda lives-in S1) and (Carla lives-in S2))"    
  nitpick[satisfy] oops

(*** Do we run into Paradoxes with the modelling of modalities? ***)

consts It_holds_that_One_plus_One_Equals_Two::bool
       It_holds_that_Fermats_last_Theorem_is_True::bool

lemma Question8:
  assumes
   "It_holds_that_One_plus_One_Equals_Two" 
   "It_holds_that_Fermats_last_Theorem_is_True" 
   "Carla says It_holds_that_One_plus_One_Equals_Two"
  shows
   "Carla says It_holds_that_Fermats_last_Theorem_is_True"  
  sledgehammer [verbose](assms)
  nitpick oops

lemma Question9:
  assumes
   "It_holds_that_One_plus_One_Equals_Two" 
   "It_holds_that_Fermats_last_Theorem_is_True" 
   "Carla knows It_holds_that_One_plus_One_Equals_Two"
  shows
   "Carla knows It_holds_that_Fermats_last_Theorem_is_True"  
  sledgehammer [verbose](assms)
  nitpick oops
end