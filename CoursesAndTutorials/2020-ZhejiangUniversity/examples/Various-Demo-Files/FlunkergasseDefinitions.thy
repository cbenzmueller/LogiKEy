theory FlunkergasseDefinitions imports Main
begin
 (*Unimportant.*) 


datatype Dorfkinder = Nilda | Carla
datatype Dorfgassen = Flunkergasse | Ehrlichergasse
 

consts wohnt_in_der::"Dorfkinder\<Rightarrow>Dorfgassen\<Rightarrow>bool" ("_ wohnt-in-der _") 
consts sagt::"Dorfkinder\<Rightarrow>bool\<Rightarrow>bool"  ("_ sagt _") 

definition und ("_ und _") where "X und Y \<equiv> X \<and> Y"

definition nicht ("nicht _") where "nicht X \<equiv> \<not>X"

definition wenn_dann ("Wenn _ dann _") where "Wenn X dann Y \<equiv> X \<longrightarrow> Y"


definition wohnt_nicht_in_der ("_ wohnt-nicht-in-der _") 
  where "X wohnt-nicht-in-der G \<equiv> nicht X wohnt-in-der G"

definition weder_noch_wohnen_in ("weder _ noch _ wohnen-in-der _") 
  where "weder X noch Y wohnen-in-der G \<equiv> 
     (nicht X wohnt-in-der G) und (nicht Y wohnt-in-der G)"

definition sowohl_als_auch_wohnen_in ("sowohl _ als auch _ wohnen-in-der _") 
  where "sowohl X als auch Y wohnen-in-der G \<equiv> 
     (X wohnt-in-der G) und (Y wohnt-in-der G)"


definition luegt ("luegt _") 
  where "luegt X \<equiv> \<forall>Y. Wenn (X sagt Y) dann nicht Y"

definition sagt_die_Wahrheit ("sagt-die-Wahrheit _") 
  where "sagt-die-Wahrheit X \<equiv> \<forall>Y. Wenn (X sagt Y) dann Y" 


named_theorems Defs
declare
 nicht_def [Defs]
 und_def [Defs]
 wenn_dann_def [Defs]
 wohnt_nicht_in_der_def [Defs]  
 weder_noch_wohnen_in_def [Defs]
 sowohl_als_auch_wohnen_in_def [Defs]
 luegt_def [Defs] 
 sagt_die_Wahrheit_def [Defs] 
end