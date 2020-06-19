theory Pierson    (*** Benzmüller, Fuenmayor & Lomfeld, 2020 ***)  
  imports GeneralKnowledge
begin (*** Pierson v. Post "wild animal" case **)

consts \<alpha>::"e" (*appropriated animal (fox in this case) *)

(*case-specific 'world-vocabulary'*)
consts Pursue::"c\<Rightarrow>e\<Rightarrow>\<sigma>"
consts Capture::"c\<Rightarrow>e\<Rightarrow>\<sigma>"

(*case-specific taxonomic (legal domain) knowledge*)
axiomatization where 
 CW1: "\<lfloor>(\<^bold>\<exists>c. Capture c \<alpha> \<^bold>\<and> \<^bold>\<not>Domestic \<alpha>) \<^bold>\<rightarrow> appWildAnimal\<rfloor>" and
 CW2: "\<lfloor>\<^bold>\<forall>c. Pursue c \<alpha> \<^bold>\<rightarrow> Intent c\<rfloor>" and
 CW3: "\<lfloor>\<^bold>\<forall>c. Capture c \<alpha> \<^bold>\<rightarrow> Poss c\<rfloor>"

lemma True nitpick[satisfy,card i=4] oops (*satisfiable*)

(****************** pro-Pierson's argument ****************)  
abbreviation "Pierson_facts \<equiv> \<lfloor>Fox \<alpha> \<^bold>\<and> (FreeRoaming \<alpha>) \<^bold>\<and> 
  (\<^bold>\<not>Pet \<alpha>) \<^bold>\<and> Pursue p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursue d \<alpha>) \<^bold>\<and> Capture d \<alpha>\<rfloor>"

(*decision for defendant (Pierson) is compatible with premises*)
lemma "Pierson_facts \<and> \<lfloor>\<^bold>\<not>INCONS\<^sup>d\<rfloor> \<and> \<lfloor>For p \<^bold>\<prec> For d\<rfloor>"
  nitpick[satisfy,card i=4] oops (* (non-trivial) model found*)

(*decision for plaintiff (Post) is compatible with premises*)
lemma "Pierson_facts \<and> \<lfloor>\<^bold>\<not>INCONS\<^sup>p\<rfloor> \<and> \<lfloor>For d \<^bold>\<prec> For p\<rfloor>"
  nitpick[satisfy,card i=4] oops (* (non-trivial) model found*)

(*decision for defendant (Pierson) is provable*)
lemma assumes Pierson_facts shows "\<lfloor>For p \<^bold>\<prec> For d\<rfloor>"
 by (metis assms CW1 CW2 W6 W8 ForAx L2 R1 other.simps(2) rBR)
(*while a decision for the plaintiff is not*)
lemma assumes Pierson_facts shows "\<lfloor>For d \<^bold>\<prec> For p\<rfloor>"
 nitpick[card i=4] oops (*counterexample found*)

(****************** pro-Post's argument ****************)
(* Theory amendment: the animal is not free-roaming since it
   is being chased by a professional hunter (Post) *)
consts Hunter::"c\<Rightarrow>\<sigma>"
axiomatization where (*case-specific legal rule for hunters*)
 CL1: "\<lfloor>(Hunter x \<^bold>\<and> Pursue x \<alpha>)  \<^bold>\<rightarrow> (STAB\<^sup>x\<inverse> \<^bold>\<prec>\<^sub>v EFFI\<^sup>x)\<rfloor>"

abbreviation "Post_facts \<equiv> \<lfloor>Fox \<alpha> \<^bold>\<and> (\<^bold>\<not>FreeRoaming \<alpha>) \<^bold>\<and>
   Hunter p \<^bold>\<and> Pursue p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursue d \<alpha>) \<^bold>\<and> Capture d \<alpha>\<rfloor>"

(*decision for defendant (Pierson) is compatible with premises*)
lemma "Post_facts \<and> \<lfloor>\<^bold>\<not>INCONS\<^sup>d\<rfloor> \<and> \<lfloor>For p \<^bold>\<prec> For d\<rfloor>"
  nitpick[satisfy,card i=4] oops (* (non-trivial) model found*)

(*decision for plaintiff (Post) is compatible with premises too*)
lemma "Post_facts \<and> \<lfloor>\<^bold>\<not>INCONS\<^sup>p\<rfloor> \<and> \<lfloor>For d \<^bold>\<prec> For p\<rfloor>"
  nitpick[satisfy,card i=4] oops (* (non-trivial) model found*)

(*indeed, a decision for plaintiff (Post) now becomes provable*)
lemma assumes Post_facts shows "\<lfloor>For d \<^bold>\<prec> For p\<rfloor>"
  using assms by (metis CW3 ForAx CL1 R3 other.simps rBR)
(*while a decision for the defendant is now refutable*)
lemma assumes Post_facts shows "\<lfloor>For p \<^bold>\<prec> For d\<rfloor>" 
  nitpick[card i=4] oops (* counterexample found*)
end