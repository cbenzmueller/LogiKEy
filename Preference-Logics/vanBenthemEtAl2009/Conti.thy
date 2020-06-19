theory Conti      (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports GeneralKnowledgeNew
begin (*** ASPCA v. Conti "wild animal" case **)

consts \<alpha>::"e" (*appropriated animal (parrot in this case) *)

(*case-specific 'world-vocabulary'*)
consts Care::"c\<Rightarrow>e\<Rightarrow>\<sigma>"
consts Prop::"c\<Rightarrow>e\<Rightarrow>\<sigma>"
consts Capture::"c\<Rightarrow>e\<Rightarrow>\<sigma>"

(*case-specific taxonomic (legal domain) knowledge*)
axiomatization where 
 CW1: "\<lfloor>Animal \<alpha> \<^bold>\<and> Pet \<alpha> \<^bold>\<rightarrow> Domestic \<alpha>\<rfloor>" and
 CW2: "\<lfloor>(\<^bold>\<exists>c. Capture c \<alpha> \<^bold>\<and> Domestic \<alpha>) \<^bold>\<rightarrow> appDomAnimal\<rfloor>" and
 CW3: "\<lfloor>\<^bold>\<forall>c. Care c \<alpha> \<^bold>\<rightarrow> Intent c\<rfloor>" and
 CW4: "\<lfloor>\<^bold>\<forall>c. Prop c \<alpha> \<^bold>\<rightarrow> Own c\<rfloor>" and
 CW5: "\<lfloor>\<^bold>\<forall>c. Capture c \<alpha> \<^bold>\<rightarrow> Poss c\<rfloor>"

lemma True nitpick[satisfy,card i=4] oops (*satisfiable*)

(****************** pro-ASPCA's argument ****************)  
abbreviation "ASPCA_facts \<equiv> \<lfloor>Parrot \<alpha> \<^bold>\<and> Pet \<alpha> \<^bold>\<and> Care p \<alpha> \<^bold>\<and> 
                     Prop p \<alpha> \<^bold>\<and> (\<^bold>\<not>Prop d \<alpha>) \<^bold>\<and> Capture d \<alpha>\<rfloor>"

lemma "ASPCA_facts" nitpick[satisfy] oops (*TODO facts inconsistent - fix*)

(* a decision for defendant (Conti) is compatible with premises*)
lemma "ASPCA_facts \<and> \<lfloor>For p \<^bold>\<prec> For d\<rfloor>"
  nitpick[satisfy,card i=4] oops (*non-trivial model*)

(* a decision for plaintiff (ASPCA) is compatible with premises*)
lemma "ASPCA_facts \<and> \<lfloor>For d \<^bold>\<prec> For p\<rfloor>"
  nitpick[satisfy,card i=4] oops (* non-trivial model?*)

(* a decision for plaintiff (ASPCA) is provable*)
lemma assumes ASPCA_facts shows "\<lfloor>For d \<^bold>\<prec> For p\<rfloor>" 
  sledgehammer
  oops
(*  while a decision for the defendant is countersatisfiable*)
lemma assumes ASPCA_facts shows "\<lfloor>For p \<^bold>\<prec> For d\<rfloor>"
  nitpick oops (*counterexample found*)

(****************** pro-Conti's argument ****************)
(*TODO ...*)

end


