theory LiarsStreet  (*Christoph Benzmüller, 2020*)
  imports Main  

(*
abbrevs   
 Nilda="\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a" and Nilda="\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a" and And="( \<^bold>a\<^bold>n\<^bold>d )" and Or="( \<^bold>o\<^bold>r )" and Not="(\<^bold>n\<^bold>o\<^bold>t )" and If_then="(\<^bold>I\<^bold>f \<^bold>t\<^bold>h\<^bold>e\<^bold>n )"
 and LiarsStreet="\<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t" and TruthtellersRoad="\<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d" and Lies="\<^bold>(l\<^bold>i\<^bold>e\<^bold>s )"
 and Says_the_truth="(\<^bold>s\<^bold>a\<^bold>y\<^bold>s\<^bold>-\<^bold>t\<^bold>h\<^bold>e\<^bold>-\<^bold>t\<^bold>r\<^bold>u\<^bold>t\<^bold>h )" and Lives_not_in="( \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>n\<^bold>o\<^bold>t\<^bold>-\<^bold>i\<^bold>n )" 
 and Neither_nor_live_in="( \<^bold>n\<^bold>e\<^bold>i\<^bold>t\<^bold>h\<^bold>e\<^bold>r  \<^bold>n\<^bold>o\<^bold>r  \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n )" and Both_live_in="( \<^bold>\<^bold>b\<^bold>o\<^bold>t\<^bold>h  \<^bold>a\<^bold>n\<^bold>d  \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n )" 
*)

begin          
(*unimportant*) nitpick_params [user_axioms,format=2,show_all]
(*unimportant*) declare [[show_abbrevs=false]]

(***********************************************************************************
 ******************  Some Basic Types of our Ontology ******************************
 ***********************************************************************************)
(* There are some kids, could be many more *)
datatype Entity = Nilda ("\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a") | Carla  ("\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a")
print_theorems

lemma "\<not>(\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a = \<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a)" sledgehammer by simp

(* There are some roads, could be many more *)
datatype Street = LiarsStreet ("\<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t") | TruthtellersRoad ("\<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d") 

(***********************************************************************************
 ******************  Controlled Natural Language Library ***************************
 ******************  Logic and Modalities ******************************************
 ***********************************************************************************)

definition And ("_ \<^bold>a\<^bold>n\<^bold>d _") where "X \<^bold>a\<^bold>n\<^bold>d Y \<equiv> X \<and> Y"
abbreviation Or ("_ \<^bold>o\<^bold>r _") where "X \<^bold>o\<^bold>r Y \<equiv> X \<or> Y"
definition Not ("\<^bold>n\<^bold>o\<^bold>t _") where "\<^bold>n\<^bold>o\<^bold>t X \<equiv> \<not>X"
definition If_then ("\<^bold>I\<^bold>f _ \<^bold>t\<^bold>h\<^bold>e\<^bold>n _") where "\<^bold>I\<^bold>f X \<^bold>t\<^bold>h\<^bold>e\<^bold>n Y \<equiv> X \<longrightarrow> Y"


(* "Says" "Knows" "Belief" "Obligation", etc. as uninterpreted truth-functions
   --- which, of course, will lead to known paradoxes *)
consts  Says::"Entity\<Rightarrow>bool\<Rightarrow>bool"  ("_ \<^bold>s\<^bold>a\<^bold>y\<^bold>s _") 
consts  Knows::"Entity\<Rightarrow>bool\<Rightarrow>bool"  ("_ \<^bold>k\<^bold>n\<^bold>o\<^bold>w\<^bold>s _")  
consts  Believes::"Entity\<Rightarrow>bool\<Rightarrow>bool"  ("_ \<^bold>b\<^bold>e\<^bold>l\<^bold>i\<^bold>e\<^bold>v\<^bold>e\<^bold>s _")    
consts  Obligation::"Entity\<Rightarrow>bool\<Rightarrow>bool"  ("_ \<^bold>m\<^bold>u\<^bold>s\<^bold>t\<^bold>-\<^bold>d\<^bold>o _") 

(* We can introduce some further derived modal NL phrases *)
definition Lies ("\<^bold>l\<^bold>i\<^bold>e\<^bold>s _") where "\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<equiv> \<forall>Y. \<^bold>I\<^bold>f (X \<^bold>s\<^bold>a\<^bold>y\<^bold>s Y) \<^bold>t\<^bold>h\<^bold>e\<^bold>n \<^bold>n\<^bold>o\<^bold>t Y"
definition Says_the_truth ("\<^bold>s\<^bold>a\<^bold>y\<^bold>s\<^bold>-\<^bold>t\<^bold>h\<^bold>e\<^bold>-\<^bold>t\<^bold>r\<^bold>u\<^bold>t\<^bold>h _") 
  where "\<^bold>s\<^bold>a\<^bold>y\<^bold>s\<^bold>-\<^bold>t\<^bold>h\<^bold>e\<^bold>-\<^bold>t\<^bold>r\<^bold>u\<^bold>t\<^bold>h X \<equiv> \<forall>Y. \<^bold>I\<^bold>f (X \<^bold>s\<^bold>a\<^bold>y\<^bold>s Y) \<^bold>t\<^bold>h\<^bold>e\<^bold>n Y" 

(* We add the above defintions to our "bag" called "Defs" — Unimportant *)
named_theorems Defs
declare Lies_def [Defs] Says_the_truth_def [Defs] 


(***********************************************************************************
 ****************** Controlled Natural Language Library ****************************
 ****************** Domain specific concepts ***************************************
 ***********************************************************************************)

(* Uninterpreted predicate: Lives_in *)
consts Lives_in::"Entity\<Rightarrow>Street\<Rightarrow>bool" ("_ \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n _") 

(* Further derived NL phrases that concern "Lives_in" *)
definition Lives_not_in ("_ \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>n\<^bold>o\<^bold>t\<^bold>-\<^bold>i\<^bold>n _")
  where "X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>n\<^bold>o\<^bold>t\<^bold>-\<^bold>i\<^bold>n G \<equiv> \<^bold>n\<^bold>o\<^bold>t (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n G)"
definition Neither_nor_live_in ("\<^bold>n\<^bold>e\<^bold>i\<^bold>t\<^bold>h\<^bold>e\<^bold>r _ \<^bold>n\<^bold>o\<^bold>r _ \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n _") 
  where "\<^bold>n\<^bold>e\<^bold>i\<^bold>t\<^bold>h\<^bold>e\<^bold>r X \<^bold>n\<^bold>o\<^bold>r Y \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n G \<equiv> (\<^bold>n\<^bold>o\<^bold>t (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n G)) \<^bold>a\<^bold>n\<^bold>d (\<^bold>n\<^bold>o\<^bold>t (Y \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n G))"
definition Both_live_in ("\<^bold>b\<^bold>o\<^bold>t\<^bold>h _ \<^bold>a\<^bold>n\<^bold>d _ \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n _") 
  where "\<^bold>b\<^bold>o\<^bold>t\<^bold>h X \<^bold>a\<^bold>n\<^bold>d Y \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n G \<equiv> (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n G) \<^bold>a\<^bold>n\<^bold>d (Y \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n G)"

(* We add the above defintions to our "bag" called "Defs" — Unimportant *)
declare Lives_not_in_def [Defs] Neither_nor_live_in_def [Defs] Both_live_in_def [Defs] 


(***********************************************************************************
 ****************** Example Queries ************************************************
 ***********************************************************************************)

axiomatization where
A1:  "\<forall>X. \<^bold>I\<^bold>f (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t) \<^bold>t\<^bold>h\<^bold>e\<^bold>n (\<^bold>l\<^bold>i\<^bold>e\<^bold>s X)"  and
A2:  "\<forall>X. \<^bold>I\<^bold>f (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d) \<^bold>t\<^bold>h\<^bold>e\<^bold>n (\<^bold>s\<^bold>a\<^bold>y\<^bold>s\<^bold>-\<^bold>t\<^bold>h\<^bold>e\<^bold>-\<^bold>t\<^bold>r\<^bold>u\<^bold>t\<^bold>h X)" 


lemma Question1:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d)" 
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"         
  nitpick[satisfy] oops  



lemma Question1b:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d)" 
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"         
  nitpick[satisfy] oops 

lemma Question2:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"  
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>n\<^bold>e\<^bold>i\<^bold>t\<^bold>h\<^bold>e\<^bold>r \<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>n\<^bold>o\<^bold>r \<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"         
  nitpick[satisfy] oops

lemma Question3:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)" 
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)" 
 shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"    
  nitpick[satisfy] oops

(*** Do we run into Paradoxes with the modelling of modalities? ***)

consts It_holds_that_One_plus_One_Equals_Two::bool
       It_holds_that_Fermats_last_Theorem_is_True::bool



lemma Question8:
  assumes
   "It_holds_that_One_plus_One_Equals_Two" 
   "It_holds_that_Fermats_last_Theorem_is_True" 
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s It_holds_that_One_plus_One_Equals_Two"
  shows
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s It_holds_that_Fermats_last_Theorem_is_True"  
  using assms(1) assms(2) assms(3) by auto


lemma Question9:
  assumes
   "It_holds_that_One_plus_One_Equals_Two" 
   "It_holds_that_Fermats_last_Theorem_is_True" 
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>k\<^bold>n\<^bold>o\<^bold>w\<^bold>s It_holds_that_One_plus_One_Equals_Two"
  shows
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>k\<^bold>n\<^bold>o\<^bold>w\<^bold>s It_holds_that_Fermats_last_Theorem_is_True"  
  sledgehammer [verbose](assms)
  nitpick oops

end