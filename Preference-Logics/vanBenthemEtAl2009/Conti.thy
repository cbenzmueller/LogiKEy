theory Conti     (*** Benzmüller, Fuenmayor & Lomfeld, 2020 ***)  
  imports GeneralKnowledge
begin (*** ASPCA v. Conti "wild animal" case **)

(*case-specific 'world-vocabulary'*)
consts \<alpha>::"e" (*appropriated animal (parrot in this case) *)
consts Care::"c\<Rightarrow>e\<Rightarrow>\<sigma>"
consts Prop::"c\<Rightarrow>e\<Rightarrow>\<sigma>"
consts Capture::"c\<Rightarrow>e\<Rightarrow>\<sigma>"

(*case-specific taxonomic (legal domain) knowledge*)
axiomatization where 
 CW1: "\<lfloor>Animal \<alpha> \<^bold>\<and> Pet \<alpha> \<^bold>\<rightarrow> Domestic \<alpha>\<rfloor>" and
 CW2: "\<lfloor>(\<^bold>\<exists>c. Capture c \<alpha> \<^bold>\<and> Domestic \<alpha>) \<^bold>\<rightarrow> appDomAnimal\<rfloor>" and
 CW3: "\<lfloor>\<^bold>\<forall>c. Care c \<alpha> \<^bold>\<rightarrow> Mtn c\<rfloor>" and
 CW4: "\<lfloor>\<^bold>\<forall>c. Prop c \<alpha> \<^bold>\<rightarrow> Own c\<rfloor>" and
 CW5: "\<lfloor>\<^bold>\<forall>c. Capture c \<alpha> \<^bold>\<rightarrow> Poss c\<rfloor>"

lemma True nitpick[satisfy,card i=4] oops (*satisfiable*)

(****************** pro-ASPCA's argument ****************)  
abbreviation "ASPCA_facts \<equiv> \<lfloor>Parrot \<alpha> \<^bold>\<and> Pet \<alpha> \<^bold>\<and> Care p \<alpha> \<^bold>\<and> 
                     Prop p \<alpha> \<^bold>\<and> (\<^bold>\<not>Prop d \<alpha>) \<^bold>\<and> Capture d \<alpha>\<rfloor>"

(* decision for defendant (Conti) is compatible with premises*)
lemma "ASPCA_facts \<and> \<lfloor>\<^bold>\<not>INCONS\<^sup>p\<rfloor> \<and> \<lfloor>\<^bold>\<not>INCONS\<^sup>d\<rfloor> \<and> \<lfloor>For p \<^bold>\<prec> For d\<rfloor>"
  nitpick[satisfy,card i=4] oops (* (non-trivial) model found*)

(* decision for plaintiff (ASPCA) is compatible with premises*)
lemma "ASPCA_facts \<and> \<lfloor>\<^bold>\<not>INCONS\<^sup>p\<rfloor> \<and> \<lfloor>\<^bold>\<not>INCONS\<^sup>d\<rfloor> \<and> \<lfloor>For d \<^bold>\<prec> For p\<rfloor>"
  nitpick[satisfy,card i=4] oops (* (non-trivial) model found*)

(* decision for plaintiff (ASPCA) is provable*)
lemma aux: assumes ASPCA_facts shows "\<lfloor>(STAB\<^sup>d \<^bold>\<prec>\<^sub>v RELI\<^sup>p\<^bold>\<oplus>RESP\<^sup>p)\<rfloor>"
  using CW1 CW2 W7 assms R3 by fastforce
theorem assumes ASPCA_facts shows "\<lfloor>For d \<^bold>\<prec> For p\<rfloor>"  
  using assms aux CW5 ForAx F3 other.simps(1) rBR by metis

(* while a decision for the defendant is refutable*)
lemma assumes ASPCA_facts shows "\<lfloor>For p \<^bold>\<prec> For d\<rfloor>"
  nitpick[card i=4] oops (*(non-trivial) counterexample found*)
end

