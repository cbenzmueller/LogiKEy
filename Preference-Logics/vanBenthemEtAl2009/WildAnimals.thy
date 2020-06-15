theory WildAnimals      (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports GeneralOntology 
begin
typedecl e  (*entities*)
(*case-specific 'world-vocabulary'*)
consts Animal::"e\<Rightarrow>\<sigma>" 
consts Domestic::"e\<Rightarrow>\<sigma>" 
consts Fox::"e\<Rightarrow>\<sigma>" 
consts Pet::"e\<Rightarrow>\<sigma>" 
consts Parrot::"e\<Rightarrow>\<sigma>" 
consts Captures::"c\<Rightarrow>e\<Rightarrow>\<sigma>" 
consts \<alpha>::"e" (*appropriated animal (fox, parrot, whale, etc.*)

(*meaning postulates for the case-specific notions above*)
axiomatization where 
CW1: "\<lfloor>\<^bold>\<forall>x. Parrot x \<^bold>\<rightarrow> Domestic x\<rfloor>" and 
CW2: "\<lfloor>\<^bold>\<forall>x. (Fox x \<^bold>\<and> Pet x) \<^bold>\<rightarrow> Domestic x\<rfloor>" and
CW3: "\<lfloor>\<^bold>\<forall>x. (Fox x \<^bold>\<and> \<^bold>\<not>Pet x) \<^bold>\<rightarrow> \<^bold>\<not>Domestic x\<rfloor>" and
CW4: "\<lfloor>((\<^bold>\<not>Domestic \<alpha>) \<^bold>\<and> (\<^bold>\<exists>c. Captures c \<alpha>)) \<^bold>\<rightarrow> appWildAnimal\<rfloor>" and
CW5: "\<lfloor>((Domestic \<alpha>) \<^bold>\<and> (\<^bold>\<exists>c. Captures c \<alpha>)) \<^bold>\<rightarrow> appDomAnimal\<rfloor>" 
(* ... others*)

lemma True nitpick[satisfy,card i=4] oops (*satisfiable*)

(*case-specific notions, cf. legal 'factors'*)
consts Pursues::"c\<Rightarrow>e\<Rightarrow>\<sigma>" (*c is pursuing an animal*)
consts OwnLand::"c\<Rightarrow>\<sigma>"    (*event takes place on c's own land *)
(*remark: Pursues will later be related to WILL, OwnLand to RELI*)

(*meaning postulates for some legal 'factors'*)
axiomatization where
 CW6: "\<lfloor>(Pursues x \<alpha>) \<^bold>\<rightarrow> (Intent x)\<rfloor>"
(* ... others*)

(*case-specific legal corpus, e.g. (unconditional) value 
  preferences given ruling decisions*)
axiomatization where
 CR2: "\<lfloor>(OwnLand x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>RELI)\<rfloor>"
(* ... others*)

(*explore possible inferences (implicit knowledge)*)
lemma "\<lfloor>(\<^bold>\<exists>c. (Fox \<alpha>) \<^bold>\<and> (Captures c \<alpha>)) \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>STAB)\<rfloor>" 
  nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(\<^bold>\<exists>c. (Fox \<alpha>) \<^bold>\<and> (Captures c \<alpha>) \<^bold>\<and> Pet \<alpha>) \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>STAB)\<rfloor>" 
  nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>appDomAnimal \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>STAB)\<rfloor>" 
  nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<not>\<lfloor>(Fox \<alpha>) \<^bold>\<and> (\<^bold>\<exists>c. Captures c \<alpha>) \<^bold>\<and> (Pet \<alpha>)\<rfloor>" 
  nitpick[satisfy] nitpick oops (*contingent*) 
  (* using CW2 CW3 CW4 W2 by blast (*inconsistent SoA*) *)

(******** TODO: experimenting with cases ************)
axiomatization where 
  CONS_p:"\<lfloor>\<^bold>\<not>INCONS p\<rfloor>" and 
  CON_d:"\<lfloor>\<^bold>\<not>INCONS d\<rfloor>" 


(*Pierson v. Post*)  
abbreviation "Situation1 \<equiv> Fox \<alpha> \<^bold>\<and> Pursues p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursues d \<alpha>) \<^bold>\<and> Poss d"
abbreviation "Situation2 \<equiv> Fox \<alpha> \<^bold>\<and> Pursues p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursues d \<alpha>) \<^bold>\<and>
   Captures d \<alpha> \<^bold>\<and> (\<^bold>\<not>Captures p \<alpha>) \<^bold>\<and> Poss d \<^bold>\<and> (\<^bold>\<not>Poss p) \<^bold>\<and> (\<^bold>\<not>Pet \<alpha>) \<^bold>\<and>
   (\<^bold>\<exists>v. (V d v))" 

lemma "\<lfloor>Situation1 \<^bold>\<and> For d\<rfloor>" 
  nitpick[satisfy,show_all,card i=1] (*non-trivial model*)
  nitpick[show_all,card i=1] 
  oops  

lemma "\<lfloor>Situation1 \<^bold>\<rightarrow> For d\<rfloor>" 
  nitpick[satisfy,show_all,card i=1] (*non-trivial model*)
  nitpick[show_all,card i=1] 
  oops   

lemma "\<lfloor>Situation2 \<^bold>\<rightarrow> For d\<rfloor>" 
  nitpick[satisfy,show_all,card i=1] (*non-trivial model*)
  nitpick[show_all,card i=1] 
  oops   

lemma "\<lfloor>Situation2 \<^bold>\<and> For d\<rfloor>" 
  nitpick[satisfy,show_all,card i=1] (*non-trivial model*)
  nitpick[show_all,card i=1] 
  oops   

lemma "\<not>(\<exists>(x::i) y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z)" 
  nitpick oops (*more than 2 worlds?*)
lemma "True" nitpick[satisfy,card i=4] oops

(*Pierson v. Post*)         
lemma "\<lfloor>Fox \<alpha> \<^bold>\<and> Pursues p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursues d \<alpha>) \<^bold>\<and> Poss d \<^bold>\<and> For d\<rfloor>" 
  nitpick[satisfy,show_all,card i=1] (*non-trivial model*)
  nitpick[show_all,card i=1] 
  oops 

lemma 
  "\<lfloor>(Fox \<alpha> \<^bold>\<and> Pursues p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursues d \<alpha>) \<^bold>\<and> Poss d) \<^bold>\<rightarrow> For d\<rfloor>" 
  nitpick[show_all,card i=1] oops (*countermodel found*)

(*Conti v. ASPCA*)
lemma 
  "\<lfloor>Parrot \<alpha> \<^bold>\<and> Captures d \<alpha> \<^bold>\<and> Mtn p \<^bold>\<and> Own p \<^bold>\<and> Poss d \<^bold>\<and> For p\<rfloor>"
  nitpick[satisfy,show_all,card i=4] oops (*non-trivial model*)

lemma 
  "\<lfloor>(Parrot \<alpha> \<^bold>\<and> Captures d \<alpha> \<^bold>\<and> Mtn p \<^bold>\<and> Own p \<^bold>\<and> Poss d) \<^bold>\<rightarrow> For p\<rfloor>"
  nitpick[show_all,card i=1] oops (*countermodel found*)
end


