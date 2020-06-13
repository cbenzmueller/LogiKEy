theory WildAnimals2 imports GeneralOntology2 (*Benzm.,Fuenmayor & Lomfeld, 2020*)               
begin

typedecl e  (*entities*)
(* define case-specific 'world- vocabulary'*)
consts Animal::"e\<Rightarrow>\<sigma>" 
consts Domestic::"e\<Rightarrow>\<sigma>" 
consts Fox::"e\<Rightarrow>\<sigma>" 
consts Pet::"e\<Rightarrow>\<sigma>" 
consts Parrot::"e\<Rightarrow>\<sigma>" 
consts Captures::"c\<Rightarrow>e\<Rightarrow>\<sigma>" 
consts \<alpha>::"e" (* appropriated animal (the fox, parrot, whale, etc. in question)*)

axiomatization where (*meaning postulates for the case-specific notions above*)
CW1: "\<lfloor>\<^bold>\<forall>x. Parrot x \<^bold>\<rightarrow> Domestic x\<rfloor>" and 
CW2: "\<lfloor>\<^bold>\<forall>x. (Fox x) \<^bold>\<and> (Pet x) \<^bold>\<rightarrow> (Domestic x)\<rfloor>" and
CW3: "\<lfloor>(Fox \<alpha>) \<^bold>\<and> (\<^bold>\<exists>c. Captures c \<alpha>) \<^bold>\<rightarrow> appWildAnimal\<rfloor>" and
CW4: "\<lfloor>(Domestic \<alpha>) \<^bold>\<and> (\<^bold>\<exists>c. Captures c \<alpha>) \<^bold>\<rightarrow> appDomesticAnimal\<rfloor>" 
(* ... others*)

lemma True nitpick[satisfy,card i=4] oops (*satisfiable, axioms are consistent*)

(*case-specific notions, cf. legal 'factors'*)
consts Pursues::"c\<Rightarrow>e\<Rightarrow>\<sigma>" (*c is pursuing an animal (later related to WILL)*)
consts OwnLand::"c\<Rightarrow>\<sigma>" (*event takes place on c's own land (later related to RELI)*)

(*meaning postulates for some legal 'factors'*)
axiomatization where
 CW5: "\<lfloor>(Pursues x \<alpha>) \<^bold>\<rightarrow> (Intent x)\<rfloor>"
(* ... others*)

(*case-specific legal corpus, e.g. (unconditional) value preferences given ruling decisions*)
axiomatization where
 CR2: "\<lfloor>(OwnLand x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>RELI)\<rfloor>"
(* ... others*)

(*explore possible inferences (implicit knowledge)*)
lemma "\<exists>c. \<lfloor>((Fox \<alpha>) \<^bold>\<and> (Captures c \<alpha>)) \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>STAB)\<rfloor>" using CW3 L3 by blast
lemma "\<lfloor>appDomesticAnimal \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>STAB)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<not>\<lfloor>(Fox \<alpha>) \<^bold>\<and> (\<^bold>\<exists>c. Captures c \<alpha>) \<^bold>\<and> (Pet \<alpha>)\<rfloor>" using CW2 CW3 CW4 W2 by blast (*inconsistent SoA*) 

(******** TODO: experimenting with cases ************)
(* axiomatization where CONSISTENT_p:"\<lfloor>\<^bold>\<not>INCONS p\<rfloor>" and CONSISTENT_d:"\<lfloor>\<^bold>\<not>INCONS d\<rfloor>" *)
lemma "\<not>(\<exists>(x::i) y z. \<not>(x = y) \<and> \<not>(x = z) \<and> \<not>(y = z))" nitpick oops (*more than 2 worlds?*)
lemma "True" nitpick[satisfy,card i=4] oops

(*Pierson v. Post*)         
lemma "\<lfloor>(Fox \<alpha>) \<^bold>\<and> (Pursues p \<alpha>) \<^bold>\<and> (\<^bold>\<not>Pursues d \<alpha>) \<^bold>\<and> (Poss d) \<^bold>\<and> For d\<rfloor>" 
  nitpick[satisfy,show_all,card i=4]  oops (*non-trivial models exist*)

lemma "\<lfloor>(Fox \<alpha>) \<^bold>\<and> (Pursues p \<alpha>) \<^bold>\<and> (\<^bold>\<not>Pursues d \<alpha>) \<^bold>\<and> (Poss d) \<^bold>\<rightarrow> For d\<rfloor>" 
  nitpick[show_all,card i=2] oops (*countermodel found*)

(*Conti v. ASPCA*)
lemma "\<lfloor>(Parrot \<alpha>) \<^bold>\<and> (Captures d \<alpha>) \<^bold>\<and> (Mtn p) \<^bold>\<and> (Own p) \<^bold>\<and> (Poss d) \<^bold>\<and> For p\<rfloor>"
  nitpick[satisfy,show_all,card i=4]  oops (*non-trivial models exist*)

lemma "\<lfloor>(Parrot \<alpha>) \<^bold>\<and> (Captures d \<alpha>) \<^bold>\<and> (Mtn p) \<^bold>\<and> (Own p) \<^bold>\<and> (Poss d) \<^bold>\<rightarrow> For p\<rfloor>"
  nitpick[show_all,card i=4] oops (*countermodel found*)

end
