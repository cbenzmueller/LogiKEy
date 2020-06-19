theory PiersonNew      (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports GeneralKnowledgeNew
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
abbreviation "Pierson_facts \<equiv> \<lfloor>Fox \<alpha> \<^bold>\<and> (FreeRoaming \<alpha>) \<^bold>\<and> (\<^bold>\<not>Pet \<alpha>) \<^bold>\<and> 
                        Pursue p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursue d \<alpha>) \<^bold>\<and> Capture d \<alpha>\<rfloor>"

(* a decision for defendant (Pierson) is compatible with premises*)
lemma "Pierson_facts \<and> \<lfloor>For p \<^bold>\<prec> For d\<rfloor>"
  nitpick[satisfy,card i=4] oops (*non-trivial model*)

(* a decision for plaintiff (Post) is compatible with premises*)
lemma "Pierson_facts \<and> \<lfloor>For d \<^bold>\<prec> For p\<rfloor>"
  nitpick[satisfy,card i=4] oops (* non-trivial model?*)

(* a decision for defendant (Pierson) is provable*)
lemma assumes Pierson_facts shows "\<lfloor>For p \<^bold>\<prec> For d\<rfloor>"
  using assms by (metis CW1 CW2 W6 W8 ForAx L2 R1 other.simps(2) rBR)
(*  while a decision for the plaintiff is countersatisfiable*)
lemma assumes Pierson_facts shows "\<lfloor>For d \<^bold>\<prec> For p\<rfloor>"
  nitpick oops (*counterexample found*)

(****************** pro-Post's argument ****************)

(*theory amendment: plaintiff claims to be a professional hunter*)
consts Prof::"c\<Rightarrow>\<sigma>"
axiomatization where (*case-specific legal rule*)
 CL1: "\<lfloor>(Pursue x \<alpha> \<^bold>\<and> Prof x \<^bold>\<and> Poss x\<inverse>)  \<^bold>\<rightarrow> (STAB\<^sup>x\<inverse> \<^bold>\<prec>\<^sub>v EFFI\<^sup>x)\<rfloor>"

abbreviation "Post_facts \<equiv> \<lfloor>Fox \<alpha> \<^bold>\<and> (\<^bold>\<not>Pet \<alpha>) \<^bold>\<and> Prof p \<^bold>\<and>
                        Pursue p \<alpha> \<^bold>\<and> (\<^bold>\<not>Pursue d \<alpha>) \<^bold>\<and> Capture d \<alpha>\<rfloor>"

(* a decision for plaintiff (Post) is compatible with premises*)
lemma "Post_facts \<and> \<lfloor>For d \<^bold>\<prec> For p\<rfloor>"
  nitpick[satisfy,card i=4] oops (*non-trivial model*)

(* a decision for plaintiff (Post) becomes provable*)
lemma assumes Post_facts shows "\<lfloor>For d \<^bold>\<prec> For p\<rfloor>"
  using assms by (metis CW3 ForAx CL1 R3 other.simps rBR)
(*  while a decision for the defendant is countersatisfiable*)
lemma assumes Post_facts shows "\<lfloor>For p \<^bold>\<prec> For d\<rfloor>" 
  nitpick oops (* counterexample *)

end


