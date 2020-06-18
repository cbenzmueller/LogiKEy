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
CL1: "\<lfloor>appAnimal \<^bold>\<rightarrow> (p\<upharpoonleft>STAB  \<^bold>\<prec> d\<upharpoonleft>STAB)\<rfloor>"
(* ... others as needed*)

(******************Pierson v. Post****************)  
abbreviation "Pierson_facts \<equiv> Fox \<alpha> \<^bold>\<and> (FreeRoaming \<alpha>) \<^bold>\<and> (\<^bold>\<not>Pet \<alpha>) \<^bold>\<and> 
                       Pursues p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursues d \<alpha>) \<^bold>\<and> Captures d \<alpha>" 

(* a decision for defendant (Pierson) is prima facie compatible with premises*)
lemma "\<lfloor>Pierson_facts \<^bold>\<and> For d\<rfloor>"
  nitpick[satisfy,show_all,card i=3] oops (*non-trivial model*)

(*TODO: is a decision for plaintiff (Post) prima facie compatible with premises?*)
lemma "\<lfloor>Pierson_facts \<^bold>\<and> For p\<rfloor>"
  nitpick[satisfy,show_all,card i=3] oops (*non-trivial model?*)
lemma "\<not>\<lfloor>Pierson_facts \<^bold>\<and> For p\<rfloor>"
  by (metis CW1 CW2 CW3 CW4 L2 R1 other.simps(2) rBR) (*using \<^bold>\<succ>\<^sub>E\<^sub>A variant*)
  (* nitpick oops (* countermodel? *) *)

(* TODO: (optional: by placing the burden of consistency on the plaintiff) 
a decision for the defendant (Pierson) should become provable*) 
lemma (*assumes "\<lfloor>\<^bold>\<not>INCONS p\<rfloor>"*)
      shows "\<lfloor>Pierson_facts \<^bold>\<rightarrow> For d\<rfloor>" nitpick oops (* countermodel? *)

(* TODO: and a decision for the plaintiff (Post) should become incompatible*)
lemma (*assumes "\<lfloor>\<^bold>\<not>INCONS p\<rfloor>"*)
      shows "\<lfloor>Pierson_facts \<^bold>\<rightarrow> \<^bold>\<not>For p\<rfloor>" nitpick oops (* countermodel? *) 

end


