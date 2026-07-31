(* 
Luca Pasetto, Christoph Benzmüller, and Réka Markovich. 2026.
Right on Thought, Left Private: Reasoning about Mental Privacy in LogiKEy.
*)

section \<open>Right to Mental Privacy in HOL: Tests\<close>

text \<open>\<close>

theory LMP_tests imports LMP begin 
nitpick_params[user_axioms=true,assms=true,expect=genuine]

(* lemma "\<lfloor>\<^bold>K a (\<^bold>B b \<phi>)\<rfloor>" nitpick oops  *)

(* FoT *)
lemma freedom_belief: "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>P[a\<rightarrow>b](\<^bold>B a \<phi>)) \<rfloor> )"
  (* nitpick  nitpick[satisfy] *)
  oops

(* Rtp 7 *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor>(\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>K b \<phi>)))\<rfloor> )"
  (* nitpick  nitpick[satisfy] *)
  oops

(* (8) *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor>(\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>\<diamond>(\<^bold>K b \<phi>))))\<rfloor> )"
  (* nitpick[satisfy,card ag=2, card i=2] nitpick *)
  oops

(* RtMP *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor>(\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>K b (\<^bold>B a \<phi>))))\<rfloor> )"
 (* nitpick  nitpick[satisfy]  *)
  oops

(* FoT extended *)
(* Nitpick found a model, a countermodel *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>P[a\<rightarrow>b](\<^bold>B a \<phi>)) \<^bold>\<and> (\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>K b (\<^bold>B a \<phi>)))) \<rfloor> )"
  unfolding LMP_Defs
  apply simp
  (* nitpick  nitpick[satisfy]   *)
  oops

(* Nitpick found a model, a countermodel *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>P[a\<rightarrow>b](\<^bold>B a  \<^bold>\<not>\<phi>)) \<^bold>\<and> (\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>K b (\<^bold>B a  \<^bold>\<not>\<phi>)))) \<rfloor> )"
  unfolding LMP_Defs
  apply simp
  (* nitpick  nitpick[satisfy]    *)
  oops

(* Nitpick found a model, a countermodel *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<phi>) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<phi>) )) \<^bold>\<and> (\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>K b ((<\<^bold>B a> \<phi>) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<phi>) ) ))) \<rfloor> )"
  unfolding LMP_Defs
  apply simp
   (* nitpick  nitpick[satisfy]     *)
  oops

(* Nitpick found a model, a countermodel *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>K b (\<^bold>B a \<phi>)))) \<^bold>\<and>  (\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>K b (\<^bold>B a  \<^bold>\<not>\<phi>)))) \<^bold>\<and> (\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>K b ((<\<^bold>B a> \<phi>) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<phi>) ) ))) \<rfloor> )"
  unfolding LMP_Defs
  apply simp
  (* nitpick  nitpick[satisfy]  *)
  oops




end

