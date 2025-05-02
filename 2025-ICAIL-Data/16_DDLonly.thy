theory "16_DDLonly"
  imports
  DDL
begin

consts
  compliance_req_chap2::"aiSys\<Rightarrow>\<sigma>"
  inform_com_auth::"aiSys\<Rightarrow>\<sigma>"
  kill_everyone::"aiSys\<Rightarrow>\<sigma>"

(*CTD example DDL:*)
consts 
  l::aiSys

(*interesting part: CTD; Trying to create the typical structure*)
axiomatization where
A0: "\<lfloor>(high_risk l)\<rfloor>" and
A1: "\<lfloor>\<^bold>\<forall>x::aiSys.(high_risk x) \<^bold>\<rightarrow> \<^bold>\<circle><(compliance_req_chap2 x)>\<rfloor>" and
A2: "\<lfloor>\<^bold>\<forall>x::aiSys. \<^bold>\<not>(compliance_req_chap2 x) \<^bold>\<and> (high_risk x) \<^bold>\<rightarrow> \<^bold>\<circle><(inform_com_auth x)>\<rfloor>" and
(*implicit: If the compliance with the requirements is a given, the provider is obligated to not inform authorities 
of non-compliance (since that would make no sense*)
A3: "\<lfloor>\<^bold>\<forall>x::aiSys. \<^bold>\<circle><(compliance_req_chap2 x) \<^bold>\<and> (high_risk x) \<^bold>\<rightarrow> (\<^bold>\<not>(inform_com_auth x))>\<rfloor>" and
Situation: "\<lfloor>\<^bold>\<not> (compliance_req_chap2 l)\<rfloor>\<^sub>l"

(***Some Experiments***) 
lemma True nitpick [satisfy, user_axioms, show_all] oops(*Consistency-check: Nitpick finds a model.*)


lemma "\<lfloor>\<^bold>\<circle><(inform_com_auth l)>\<rfloor>\<^sub>l" using A0 A2 Situation by auto
lemma "\<lfloor>\<^bold>\<circle><\<^bold>\<not>(inform_com_auth l)>\<rfloor>\<^sub>l" nitpick [user_axioms] oops (*counterexample found*)
lemma "\<lfloor>\<^bold>\<circle><(kill_everyone l)>\<rfloor>\<^sub>l" try oops

end


















