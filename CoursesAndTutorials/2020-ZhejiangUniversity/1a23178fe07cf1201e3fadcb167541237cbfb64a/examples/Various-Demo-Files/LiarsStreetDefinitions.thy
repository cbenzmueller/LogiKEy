theory LiarsStreetDefinitions imports Main
begin
 (*Unimportant.*) 


datatype Kids = Nilda | Carla
datatype Streets = LiarsStreet | TruthtellersRoad
 

consts Lives_in::"Kids\<Rightarrow>Streets\<Rightarrow>bool" ("_ lives-in _") 
consts Says::"Kids\<Rightarrow>bool\<Rightarrow>bool"  ("_ says _") 

definition And ("_ and _") where "X and Y \<equiv> X \<and> Y"

definition Not ("not _") where "not X \<equiv> \<not>X"

definition If_then ("If _ then _") where "If X then Y \<equiv> X \<longrightarrow> Y"

definition Lives_not_in ("_ lives-not-in _") 
  where "X lives-not-in G \<equiv> not (X lives-in G)"

definition Neither_nor_live_in ("neither _ nor _ live-in _") 
  where "neither X nor Y live-in G \<equiv> 
     (not (X lives-in G)) and (not (Y lives-in G))"

definition Both_live_in ("both _ and _ live-in _") 
  where "both X and Y live-in G \<equiv> 
     (X lives-in G) and (Y lives-in G)"

definition Lies ("lies _") 
  where "lies X \<equiv> \<forall>Y. If (X says Y) then not Y"

definition Says_the_truth ("says-the-truth _") 
  where "says-the-truth X \<equiv> \<forall>Y. If (X says Y) then Y" 

named_theorems Defs
declare
 Not_def [Defs]
 And_def [Defs]
 If_then_def [Defs]
 Lives_not_in_def [Defs]  
 Neither_nor_live_in_def [Defs]
 Both_live_in_def [Defs]
 Lies_def [Defs] 
 Says_the_truth_def [Defs] 
end