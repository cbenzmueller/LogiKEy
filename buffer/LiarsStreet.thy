theory LiarsStreet imports  LiarsStreetDefinitions   (*Christoph Benzmüller, 2019*)
begin          
                (*unimportant*) nitpick_params [user_axioms,format=2,show_all]

axiomatization where
A1:  "\<forall>X. If (X lives-in LiarsStreet) then (lies X)"  and
A2:  "\<forall>X. If (X lives-in TruthtellersRoad) then (says-the-truth X)" 

lemma Question1:
  assumes
   "Nilda says (Carla lives-in TruthtellersRoad)" 
   "Carla says (Nilda lives-in TruthtellersRoad)"
  shows
   (* "\<exists> S1 S2. ((Nilda lives-in S1) and (Carla lives-in S2))" *)
   "\<exists> S1 S2. (((Nilda lives-in S1) and (Carla lives-in S2)) and (not (S1 = TruthtellersRoad)))" 
  
  nitpick[satisfy] oops 

lemma "\<exists> S1 S2. (((Nilda lives-in S1) and (Carla lives-in S2)) and (not (S1 = TruthtellersRoad)))" 
  nitpick[satisfy] oops 

lemma Question2:
  assumes
   "Nilda says (Carla lives-in LiarsStreet)"  
   "Carla says (neither Nilda nor Carla live-in LiarsStreet)"
  shows
   "\<exists> S1 S2. ((Nilda lives-in S1) and (Carla lives-in S2))"             
  nitpick[satisfy] oops



lemma Question3:
  assumes
   "Nilda says (Carla lives-in LiarsStreet)" 
   "Carla says (Carla lives-in LiarsStreet)" 
 shows
   "\<exists> S1 S2. ((Nilda lives-in S1) and (Carla lives-in S2))"    
  nitpick[satisfy] oops



consts A::bool B::bool
lemma Question4:
  assumes
   "A" 
   "B" 
   "Carla says A"
  shows
   "Carla says B"  

  sledgehammer
  nitpick oops



consts Knows::"Kids\<Rightarrow>bool\<Rightarrow>bool"  ("_ knows _") 

lemma Question5:
  assumes
   "A"
   "B" 
   "Carla knows A"
  shows
   "Carla knows B"  

  sledgehammer
  nitpick oops
end