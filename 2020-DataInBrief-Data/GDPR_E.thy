theory GDPR_E imports E       (*GDPR CTD Example. C. Benzmüller & X. Parent, 2019*)
begin
(*Unimportant.*) sledgehammer_params [max_facts=20,timeout=20] 
(*Unimportant.*) nitpick_params [user_axioms,expect=genuine,show_all,dont_box]

datatype data = d1 | d2   (*We introduce concrete data objects d1 and d2.*)
datatype indiv = Mary | Peter (*We introduce individuals Mary and Peter.*)
consts process_lawfully::"data\<Rightarrow>\<sigma>" erase::"data\<Rightarrow>\<sigma>" is_protected_by_GDPR::"data\<Rightarrow>\<sigma>" 
       belongs_to::"data\<Rightarrow>indiv\<Rightarrow>\<sigma>" is_european::"indiv=>\<sigma> " kill::"indiv\<Rightarrow>\<sigma>"

axiomatization where
(*Data belonging to Europeans is protected by the GDPR.*)
 A0: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>d. (is_european x \<^bold>\<and> belongs_to d x) \<^bold>\<rightarrow> is_protected_by_GDPR d\<rfloor>" and
(*Data d1 is belonging to the European Peter.*)
 F1: "\<lfloor>belongs_to d1 Peter \<^bold>\<and> is_european Peter\<rfloor>" and

(*It is an obligation to process data lawfully.*)
 A1: "\<lfloor>\<^bold>\<forall>d. \<circle><process_lawfully d | is_protected_by_GDPR d>\<rfloor>"  and
(*If data was not processed lawfully, then it is an obligation to erase the data.*)
 A2: "\<lfloor>\<^bold>\<forall>d. \<circle><erase d | is_protected_by_GDPR d  \<^bold>\<and> \<^bold>\<not>process_lawfully d>\<rfloor>" and
(*Implicit: It is an obligation to keep the data if it was processed lawfully.*)
 Implicit: "\<lfloor>\<^bold>\<forall>d. \<circle><\<^bold>\<not>erase d | is_protected_by_GDPR d \<^bold>\<and> process_lawfully d>\<rfloor>" and
(*Given a situation where data is processed unlawfully.*) 
 Situation: "\<lfloor>\<^bold>\<not>process_lawfully d1\<rfloor>\<^sub>l" 


(***Some Experiments***) 
 lemma True nitpick [satisfy] oops (*Consistency-check: Nitpick finds a model.*) 
 lemma False sledgehammer oops (*Inconsistency-check: Can Falsum be derived? No.*) 

 lemma "\<lfloor>\<^bold>\<circle><erase d1>\<rfloor>\<^sub>l" nitpick oops (*Should the data be erased? — No. Countermodel by Nitpick.*)
 lemma "\<lfloor>\<^bold>\<circle><\<^bold>\<not>erase d1>\<rfloor>\<^sub>l" sledgehammer using A0 A1 F1 Implicit by blast (*Should the data be kept? — Yes.*)
 lemma "\<lfloor>\<^bold>\<circle><kill Mary>\<rfloor>\<^sub>l" nitpick oops (*Should Mary be killed? — No. Countermodel by Nitpick.*)
end