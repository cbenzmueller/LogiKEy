section \<open>Right to Privacy in HOL\<close>

text \<open>\<close>

theory LRP imports PMML begin 
nitpick_params[user_axioms=true,assms=true,expect=genuine]

(* epistemic modality *)
consts ag_k::"ag\<Rightarrow>\<gamma>" (* links agents to accessibility relations *)
definition mknow::"ag\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>K_ _") 
  where "\<^bold>K x \<phi> \<equiv> \<lambda>w.\<forall>v. ((ag_k x) w v \<longrightarrow> \<phi> v)"
abbreviation(input) mnknow :: "ag\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("<\<^bold>K_> _")
  where "<\<^bold>K x> \<phi> \<equiv> (\<^bold>\<not>(\<^bold>K x (\<^bold>\<not> \<phi>)))"
(* equivalence relation *)
axiomatization where
  AxiomS5_know: "\<forall>x. reflexive (ag_k x) \<and> symmetric (ag_k x) \<and> transitive (ag_k x)" 
(* AxiomKT45_know: "\<forall>x.  reflexive (ag_k x) \<and> transitive (ag_k x) \<and> euclidean (ag_k x)" *)

print_theorems 

named_theorems LRP_Defs
declare
HOMML_Defs[LRP_Defs]
mknow_def[LRP_Defs]


text \<open>Consistency: nitpick reports a model.\<close>
lemma True nitpick[satisfy] oops (* model found *)


end

