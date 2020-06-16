theory Pierson      (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports GeneralKnowledge
begin (*** pro-Pierson's theory, cf. Pierson v. Post wild animal case **)

typedecl e (*type for entities*)
consts \<alpha>::"e" (*appropriated animal (fox, parrot, whale, etc.*)

(*case-specific 'world-vocabulary'*)
consts Animal::"e\<Rightarrow>\<sigma>" 
consts Domestic::"e\<Rightarrow>\<sigma>" 
consts Fox::"e\<Rightarrow>\<sigma>" 
consts Pet::"e\<Rightarrow>\<sigma>" 
consts FreeRoaming::"e\<Rightarrow>\<sigma>" 
consts Pursues::"c\<Rightarrow>e\<Rightarrow>\<sigma>"
consts Captures::"c\<Rightarrow>e\<Rightarrow>\<sigma>"

(*case-specific taxonomic (legal domain) knowledge*)
axiomatization where 
 CW1: "\<lfloor>\<^bold>\<forall>a. Fox a \<^bold>\<rightarrow> Animal a\<rfloor>" and
 CW2: "\<lfloor>\<^bold>\<forall>a. (Animal a \<^bold>\<and> FreeRoaming a \<^bold>\<and> \<^bold>\<not>Pet a) \<^bold>\<rightarrow> \<^bold>\<not>Domestic a\<rfloor>" and
 CW3: "\<lfloor>(\<^bold>\<exists>c. Captures c \<alpha> \<^bold>\<and> \<^bold>\<not>Domestic \<alpha>) \<^bold>\<rightarrow> appWildAnimal\<rfloor>" and
 CW4: "\<lfloor>\<^bold>\<forall>c. Pursues c \<alpha> \<^bold>\<rightarrow> Intent c\<rfloor>" and
 CW5: "\<lfloor>\<^bold>\<forall>c. Captures c \<alpha> \<^bold>\<rightarrow> Poss c\<rfloor>"
(* ... others as needed*)

lemma True nitpick[satisfy,card i=4] oops (*satisfiable*)

(*case-specific legal corpus*)
axiomatization where 
CL1: "\<lfloor>appAnimal \<^bold>\<rightarrow> (p\<upharpoonleft>STAB  \<^bold>\<preceq>\<^sub>A\<^sub>A d\<upharpoonleft>STAB)\<rfloor>"
(* ... others as needed*)

(******************Pierson v. Post****************)  
abbreviation "Pierson_facts \<equiv> Fox \<alpha> \<^bold>\<and> (FreeRoaming \<alpha>) \<^bold>\<and> (\<^bold>\<not>Pet \<alpha>) \<^bold>\<and> 
                       Pursues p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursues d \<alpha>) \<^bold>\<and> Captures d \<alpha>" 

(* a decision for defendant (Pierson) is prima facie compatible with premises*)
lemma "\<lfloor>Pierson_facts \<^bold>\<and> For d\<rfloor>"
  nitpick[satisfy,show_all,card i=3] oops (*non-trivial model*)

(* a decision for plaintiff (Post) is prima facie compatible with premises*)
lemma "\<lfloor>Pierson_facts \<^bold>\<and> For p\<rfloor>" 
  nitpick[satisfy,show_all,card i=3] oops (*non-trivial model*)

(* by placing the burden of consistency on the plaintiff, 
a decision for the defendant (Pierson) becomes provable*) 
lemma assumes "\<lfloor>\<^bold>\<not>INCONS p\<rfloor>" shows "\<lfloor>Pierson_facts \<^bold>\<rightarrow> For d\<rfloor>" 
  using assms by (metis CW1 CW2 CW3 CW5 CL1 ForAx L2 L5 R4 W1 other.simps(2) rBR)

(* and a decision for the plaintiff (Post) becomes incompatible*)
lemma assumes "\<lfloor>\<^bold>\<not>INCONS p\<rfloor>" shows "\<not>\<lfloor>Pierson_facts \<^bold>\<and> For p\<rfloor>" 
  using assms CW1 CW2 CW3 CW4 CW5 CL1 L5 R1 R4 W3 rBR by fastforce

end


