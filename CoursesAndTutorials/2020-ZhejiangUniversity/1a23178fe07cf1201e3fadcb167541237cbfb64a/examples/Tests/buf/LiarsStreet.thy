theory LiarsStreet imports  LiarsStreetDefinitions   (*Christoph Benzmüller, 2019*)
begin          
(*unimportant*) nitpick_params [user_axioms,format=2,show_all]

axiomatization where
A1:  "\<lfloor>Forall X. If (X lives-in LiarsStreet) then (lies X)\<rfloor>"  and
A2:  "\<lfloor>Forall X. If (X lives-in TruthtellersRoad) then (says-the-truth X)\<rfloor>" 

lemma Question1:
  assumes
   "\<lfloor>Nilda says (Carla lives-in TruthtellersRoad)\<rfloor>" 
   "\<lfloor>Carla says (Nilda lives-in TruthtellersRoad)\<rfloor>"
  shows
   "\<lfloor>((Nilda lives-in S1) and (Carla lives-in S2))\<rfloor>"       
  nitpick[satisfy] oops 

  (* lemma "\<exists> S1 S2. (((Nilda lives-in S1) and (Carla lives-in S2)) and (not (S1 = TruthtellersRoad)))" *)


lemma Question2:
  assumes
   "\<lfloor>Nilda says (Carla lives-in LiarsStreet)\<rfloor>"  
   "\<lfloor>Carla says (neither Nilda nor Carla live-in LiarsStreet)\<rfloor>"
  shows
   "\<lfloor>((Nilda lives-in S1) and (Carla lives-in S2))\<rfloor>"              
  nitpick[satisfy] oops



lemma Question3:
  assumes
   "\<lfloor>Nilda says (Carla lives-in LiarsStreet)\<rfloor>" 
   "\<lfloor>Carla says (Carla lives-in LiarsStreet)\<rfloor>" 
 shows
   "\<lfloor>((Nilda lives-in S1) and (Carla lives-in S2))\<rfloor>"    
  nitpick[satisfy] oops

lemma Question4:
  assumes
   "\<lfloor>Nilda says (Nilda says (Nilda lives-in LiarsStreet))\<rfloor>" 
 shows
   "\<lfloor>(Nilda lives-in S1)\<rfloor>"    
  nitpick[satisfy] oops

lemma Question5:
  assumes
   "\<lfloor>Nilda says (Nilda says (Nilda lives-not-in LiarsStreet))\<rfloor>" 
 shows
   "\<lfloor>(Nilda lives-in S1)\<rfloor>"    
  nitpick[satisfy] oops

lemma Question6:
  assumes
   "\<lfloor>Nilda says (Nilda says ((Nilda lives-in LiarsStreet) and (Nilda lives-in TruthtellersRoad)))\<rfloor>" 
 shows
   "\<lfloor>(Nilda lives-in S1)\<rfloor>"    
  nitpick[satisfy] oops

lemma Question7:
  assumes
   "\<lfloor>Nilda says (Carla says ((Nilda lives-in LiarsStreet) and (Nilda lives-in TruthtellersRoad)))\<rfloor>" 
 shows
   "\<lfloor>((Nilda lives-in S1) and (Carla lives-in S2))\<rfloor>"    
  nitpick[satisfy] oops

consts A::\<sigma> B::\<sigma>
lemma Question4:
  assumes
   "\<lfloor>A\<rfloor>" 
   "\<lfloor>B\<rfloor>" 
   "\<lfloor>Carla says A\<rfloor>"
  shows
   "\<lfloor>Carla says B\<rfloor>"  
  sledgehammer
  nitpick oops



consts Knows::"Kids\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("_ knows _") 

lemma Question5:
  assumes
   "\<lfloor>A\<rfloor>"
   "\<lfloor>B\<rfloor>" 
   "\<lfloor>Carla knows A\<rfloor>"
  shows
   "\<lfloor>Carla knows B\<rfloor>"  
  sledgehammer
  nitpick oops
end