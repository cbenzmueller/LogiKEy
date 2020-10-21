theory Flunkergasse imports FlunkergasseDefinitions     (* By Christoph Benzmüller, 2019 *)
begin          
                (*unimportant*) nitpick_params [user_axioms,format=2,show_all]

axiomatization where
A1:  "Wenn (Kind wohnt-in-der Flunkergasse) dann (luegt Kind)"  and
A2:  "Wenn (Kind wohnt-in-der Ehrlichergasse) dann (sagt-die-Wahrheit Kind)" 

lemma Frage1:
  assumes
   "Nilda sagt (Carla wohnt-in-der Ehrlichergasse)" 
   "Carla sagt (Nilda wohnt-in-der Ehrlichergasse)"
  shows
   "\<exists> Gasse1 Gasse2. (Nilda wohnt-in-der Gasse1 und Carla wohnt-in-der Gasse2)"       
   
   nitpick[satisfy] oops (*model found by nitpick*)

lemma Frage2:
  assumes
   "Nilda sagt (Carla wohnt-in-der Flunkergasse)" 
   "Carla sagt (weder Nilda noch Carla wohnen-in-der Flunkergasse)"
  shows
   "\<exists> Gasse1 Gasse2. (Nilda wohnt-in-der Gasse1 und Carla wohnt-in-der Gasse2)"   
     
  nitpick[satisfy] oops



lemma Frage3:
  assumes
   "Nilda sagt (Carla wohnt-in-der Flunkergasse)" 
   "Carla sagt (Nilda wohnt-in-der Flunkergasse)"
  shows
   "\<exists> Gasse1 Gasse2. (Nilda wohnt-in-der Gasse1 und Carla wohnt-in-der Gasse2)"  
     
  nitpick[satisfy] oops



lemma Frage4:
  assumes
   "Nilda sagt (Carla wohnt-in-der Flunkergasse)" 
   "Carla sagt (Nilda wohnt-in-der Ehrlichergasse)"
  shows
   "\<exists> Gasse1 Gasse2. (Nilda wohnt-in-der Gasse1 und Carla wohnt-in-der Gasse2)"  
     
  nitpick[satisfy] oops


consts A::bool B::bool
lemma Frage4:
  assumes
   "A \<longleftrightarrow> B" 
   "Carla sagt A"
  shows
   "Carla sagt B"  

  sledgehammer
  nitpick oops

end