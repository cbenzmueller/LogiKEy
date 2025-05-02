theory "24_DDLonly"
  imports 
  types
  DDL
begin

consts
  system_in_conformity::"aiSys\<Rightarrow>\<sigma>"
  not_on_market::"aiSys\<Rightarrow>\<sigma>"

(*CTD structure*)
consts l::aiSys

axiomatization where
A0: "\<lfloor>high_risk l\<rfloor>\<^sub>l" and
A1: "\<lfloor>\<^bold>\<forall>x::aiSys. (high_risk x) \<^bold>\<rightarrow> \<^bold>\<circle><(system_in_conformity x)>\<rfloor>" and 
A2: "\<lfloor>\<^bold>\<forall>x::aiSys. \<^bold>\<not> (system_in_conformity x) \<^bold>\<and> (high_risk x) \<^bold>\<rightarrow> \<^bold>\<circle><(not_on_market x)>\<rfloor>" and
(*implicit: If the system is in conformity, the importer is obligated to not see to it that the system is not placed
on the market*)
A3: "\<lfloor>\<^bold>\<forall>x::aiSys. \<^bold>\<circle><(system_in_conformity x) \<^bold>\<rightarrow> (\<^bold>\<not>(not_on_market x))>\<rfloor>" and
Situation: "\<lfloor>\<^bold>\<not> (system_in_conformity l)\<rfloor>\<^sub>l"

(***Some Experiments***) 
lemma True nitpick [satisfy, user_axioms, show_all] oops (*Consistency-check: Nitpick finds a model.*)

lemma "\<lfloor>\<^bold>\<circle><(not_on_market l)>\<rfloor>\<^sub>l" using A0 A2 Situation by auto
lemma "\<lfloor>\<^bold>\<circle><\<^bold>\<not>(not_on_market l)>\<rfloor>\<^sub>l" nitpick [user_axioms, show_all] oops (*counterexample found*)

end