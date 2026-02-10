section \<open>Freedom of Thought in HOL\<close>

text \<open>\<close>

theory LFT imports PMML begin  
nitpick_params[user_axioms=true,assms=true,expect=genuine, show_all, format=2]

(* doxastic modality *)
consts ag_b::"ag\<Rightarrow>\<gamma>" (* links agents to accessibility relations *)
definition mbel::"ag\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>B_ _") 
  where "\<^bold>B x \<phi> \<equiv> \<lambda>w.\<forall>v. ((ag_b x) w v \<longrightarrow> \<phi> v)"
abbreviation(input) mnbel :: "ag\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("<\<^bold>B_> _")
  where "<\<^bold>B x> \<phi> \<equiv> (\<^bold>\<not>(\<^bold>B x (\<^bold>\<not> \<phi>)))"
(* serial relation *)
axiomatization where
  AxiomKD_bel: "\<forall>x. serial (ag_b x)"

print_theorems 


named_theorems LFT_Defs
declare
HOMML_Defs[LFT_Defs]
mbel_def[LFT_Defs]

text \<open>Consistency: nitpick reports a model.\<close>
lemma True nitpick[satisfy] oops (* model found *)


end
