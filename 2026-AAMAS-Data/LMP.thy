section \<open>Right to Mental Privacy in HOL\<close>

text \<open>\<close>

theory LMP imports LRP LFT begin 
nitpick_params[user_axioms=true,assms=true,expect=genuine]

text \<open>Consistency: nitpick reports a model.\<close>
lemma True nitpick[satisfy, card ag=2, card i=2] oops (* model found *)

named_theorems LMP_Defs
declare
HOMML_Defs[LMP_Defs]
mknow_def[LMP_Defs]
mbel_def[LMP_Defs]

end

