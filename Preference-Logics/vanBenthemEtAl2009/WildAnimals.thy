theory WildAnimals      (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports GeneralKnowledge
begin (*** Modeling of wild animal cases from literature ***)
typedecl e (*entities*)

(*case-specific 'world-vocabulary'*)
consts Animal::"e\<Rightarrow>\<sigma>" 
consts Domestic::"e\<Rightarrow>\<sigma>" 
consts Fox::"e\<Rightarrow>\<sigma>" 
consts Pet::"e\<Rightarrow>\<sigma>" 
consts Parrot::"e\<Rightarrow>\<sigma>" 
consts Captures::"c\<Rightarrow>e\<Rightarrow>\<sigma>" 
consts \<alpha>::"e" (*appropriated animal (fox, parrot, whale, etc.*)

(*case-specific taxonomic (legal domain) knowledge*)
axiomatization where 
CW1: "\<lfloor>\<^bold>\<forall>x. Parrot x \<^bold>\<rightarrow> Domestic x\<rfloor>" and 
CW2: "\<lfloor>\<^bold>\<forall>x. (Fox x \<^bold>\<and> Pet x) \<^bold>\<rightarrow> Domestic x\<rfloor>" and
CW3: "\<lfloor>\<^bold>\<forall>x. (Fox x \<^bold>\<and> \<^bold>\<not>Pet x) \<^bold>\<rightarrow> \<^bold>\<not>Domestic x\<rfloor>" and
CW4: "\<lfloor>((\<^bold>\<not>Domestic \<alpha>) \<^bold>\<and> (\<^bold>\<exists>c. Captures c \<alpha>)) \<^bold>\<rightarrow> appWildAnimal\<rfloor>" and
CW5: "\<lfloor>((Domestic \<alpha>) \<^bold>\<and> (\<^bold>\<exists>c. Captures c \<alpha>)) \<^bold>\<rightarrow> appDomAnimal\<rfloor>" 
(*\<dots>others\<dots>*)

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
lemma "\<lfloor>(\<^bold>\<exists>c. (Fox \<alpha>) \<^bold>\<and> (Captures c \<alpha>)) \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>STAB)\<rfloor>" 
  nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(\<^bold>\<exists>c. (Fox \<alpha>) \<^bold>\<and> (Captures c \<alpha>) \<^bold>\<and> Pet \<alpha>) \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>STAB)\<rfloor>" 
  nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>appDomAnimal \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>STAB)\<rfloor>" 
  nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<not>\<lfloor>(Fox \<alpha>) \<^bold>\<and> (\<^bold>\<exists>c. Captures c \<alpha>) \<^bold>\<and> (Pet \<alpha>)\<rfloor>" 
  nitpick[satisfy] nitpick oops (*contingent*) 


(******************Pierson v. Post****************)  
abbreviation "Pierson_simple \<equiv> Fox \<alpha> \<^bold>\<and> Pursues p \<alpha> \<^bold>\<and> Poss d"
abbreviation "Pierson_complex \<equiv> Fox \<alpha> \<^bold>\<and> Pursues p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursues d \<alpha>) \<^bold>\<and>
   Captures d \<alpha> \<^bold>\<and> (\<^bold>\<not>Captures p \<alpha>) \<^bold>\<and> Poss d \<^bold>\<and> (\<^bold>\<not>Poss p) \<^bold>\<and> (\<^bold>\<not>Pet \<alpha>) \<^bold>\<and>
   (\<^bold>\<exists>v. (V d v))" 

lemma "\<lfloor>Pierson_simple \<^bold>\<and> For d\<rfloor>" (* decision for defendant (Pierson) is compatible with premises*)
  nitpick[satisfy,show_all,card i=3] oops (*non-trivial model*)

lemma "\<lfloor>Pierson_simple \<^bold>\<and> For p\<rfloor>" (* decision for plaintiff (Post) is compatible with premises*)
  nitpick[satisfy,show_all,card i=3] oops (*non-trivial model*)

lemma "\<lfloor>Pierson_simple \<^bold>\<rightarrow> For d\<rfloor>" (* decision for defendant (Pierson) is contingent*) 
  nitpick oops

lemma "\<lfloor>Pierson_simple \<^bold>\<rightarrow> For p\<rfloor>" (* decision for plaintiff (Post) is contingent*) 
  nitpick oops

lemma "\<lfloor>Pierson_complex \<^bold>\<and> For d\<rfloor>" (* decision for defendant (Pierson) is compatible with premises*)
  nitpick[satisfy,show_all,card i=3] oops (*non-trivial model*)

lemma "\<lfloor>Pierson_complex \<^bold>\<and> For p\<rfloor>" (* decision for plaintiff (Post) is compatible with premises*) 
  nitpick[satisfy,show_all,card i=3] oops (*non-trivial model*)


(*************Conti v. ASPCA****************)
abbreviation "Conti_simple \<equiv> Parrot \<alpha> \<^bold>\<and> Captures d \<alpha> \<^bold>\<and> Mtn p \<^bold>\<and> Own p \<^bold>\<and> Poss d"

lemma "\<lfloor>Conti_simple \<^bold>\<and> For p\<rfloor>" (* decision for plaintiff (ASPCA) is compatible with premises*)
   nitpick[satisfy,show_all,card i=3] oops (*non-trivial model*)

lemma "\<lfloor>Conti_simple \<^bold>\<and> For d\<rfloor>" (* decision for defendant (Conti) is compatible with premises*)
  nitpick[satisfy,show_all,card i=3] oops (*non-trivial model*)

lemma "\<lfloor>Conti_simple \<^bold>\<rightarrow> For p\<rfloor>" (* decision for plaintiff (ASPCA) is prima facie contingent...*)
   nitpick oops

lemma "\<lfloor>Conti_simple \<^bold>\<rightarrow> For d\<rfloor>" (* decision for defendant (Conti) is prima facie contingent...*)
   nitpick oops

lemma "\<lfloor>\<^bold>\<not>INCONS p\<rfloor> \<Longrightarrow> \<lfloor>Conti_simple \<^bold>\<rightarrow> For d\<rfloor>" (*...however, it becomes provable if its opponent is consistent*)
  by (smt CW1 CW5 ForAx L3 R4 other.simps(2) rBR)

lemma "\<lfloor>\<^bold>\<not>INCONS p\<rfloor> \<Longrightarrow> \<not>\<lfloor>Conti_simple \<^bold>\<and> For p\<rfloor>" (* decision for plaintiff (ASPCA) is incompatible with its consistency*)
  by (smt CW1 CW5 L3 R4 other.simps(2) rBR)

(* TODO: the decision for Conti (given consistency of ASPCA) is unexpected! debug: what went wrong?*)
lemma "\<lfloor>Conti_simple \<^bold>\<rightarrow> (d\<upharpoonleft>STAB \<^bold>\<preceq>\<^sub>A\<^sub>A p\<upharpoonleft>[RELI\<oplus>RESP])\<rfloor>" (*value preferences are as expected (domestic animals)*)
  by (metis CW1 CW5 L3 other.simps(1))

lemma "\<lfloor>Conti_simple \<^bold>\<rightarrow> For p\<rfloor>" nitpick[show_all,card i=1] oops (* case should be ruled for p: debug model*)

end


