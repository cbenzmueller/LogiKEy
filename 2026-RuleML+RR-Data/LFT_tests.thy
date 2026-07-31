(* 
Luca Pasetto, Christoph Benzmüller, and Réka Markovich. 2026.
Right on Thought, Left Private: Reasoning about Mental Privacy in LogiKEy.
*)

section \<open>Tests on Freedom of Thought in HOL\<close>

theory LFT_tests imports LFT begin
nitpick_params[user_axioms=true,assms=true,expect=genuine,show_all,format=2,mono = false,dont_box]

(* agent a *)
consts a::ag

(* 4.2.1 Freedom *)
  term "(\<^bold>P[a\<rightarrow>b](\<^bold>B a \<phi>))"
  term "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>P[a\<rightarrow>b](\<^bold>B a \<phi>)) \<rfloor> )"
(* found model, countermodel *)
lemma freedom_belief: "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>P[a\<rightarrow>b](\<^bold>B a \<phi>)) \<rfloor> )"
  nitpick[card ag=3, card i=4]   nitpick[satisfy, card ag=3, card i=4]
  oops

(* found model, countermodel *)
lemma freedom_disbelief: "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>P[a\<rightarrow>b](\<^bold>B a \<^bold>\<not>\<phi>)) \<rfloor> )"
  nitpick[card ag=3, card i=4]   nitpick[satisfy, card ag=3, card i=4]
  oops

(* found model, countermodel *)
lemma freedom_suspension: "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<phi>) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<phi>) )) \<rfloor> )"
  nitpick[card ag=3, card i=4]   nitpick[satisfy, card ag=3, card i=4]
  oops

(* found model, countermodel *)
lemma freedom_conj: "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>P[a\<rightarrow>b](\<^bold>B a \<phi>)) \<^bold>\<and> (\<^bold>P[a\<rightarrow>b](\<^bold>B a \<^bold>\<not>\<phi>)) \<^bold>\<and> (\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<phi>) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<phi>) )) \<rfloor> )"
  nitpick[card ag=3, card i=4]   nitpick[satisfy, card ag=3, card i=4]
  oops

(* other experiments *)
lemma "\<lfloor>(\<^bold>P[a\<rightarrow>b](\<^bold>B a \<phi>)) \<^bold>\<rightarrow> (\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<phi>)))\<rfloor>"
  unfolding LFT_Defs
  apply simp
  by (metis AxiomKD_bel serial_def)

(* finds a countermodel if card ag>1 *)
(* lemma "\<forall>w. a=b \<longrightarrow> (((\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<phi>) )) \<^bold>\<and> (\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<^bold>\<not> \<phi>) )))w \<longrightarrow> (\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<phi>) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<phi>) ))w)" *)
lemma "\<forall>w. (((\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<phi>) )) \<^bold>\<and> (\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<^bold>\<not> \<phi>) )))w \<longrightarrow> (\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<phi>) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<phi>) ))w)"
    unfolding LFT_Defs
    apply simp
     (* nitpick  nitpick[satisfy]   *)
    oops

(* 4.2.2 Claim-right *)
  term "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>O[b\<rightarrow>a](\<^bold>\<not> \<^bold>E b \<^bold>\<not>(\<^bold>B a \<phi>))) \<rfloor> )"
(* found model, countermodel *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>O[b\<rightarrow>a](\<^bold>\<not> \<^bold>E b \<^bold>\<not>(\<^bold>B a \<phi>))) \<rfloor> )"
  nitpick[card ag=3, card i=4]   nitpick[satisfy, card ag=3, card i=4]
  oops

  term "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>O[b\<rightarrow>a](\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a \<phi>))) \<rfloor> )"
(* found model, countermodel *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor> (\<^bold>O[b\<rightarrow>a](\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a \<phi>))) \<rfloor> )"
  nitpick[card ag=3, card i=4]   nitpick[satisfy, card ag=3, card i=4]
  oops

(* found model, countermodel *)
lemma claim_conj: "\<forall>b. ((a\<noteq>b) \<longrightarrow>
     \<lfloor> \<^bold>O[b\<rightarrow>a](
      (\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a \<phi>)) \<^bold>\<and>
      (\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a \<^bold>\<not>\<phi>)) \<^bold>\<and>
      (\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>((<\<^bold>B a> \<phi>) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<phi>) )) ) \<rfloor> )"
  nitpick[card ag=3, card i=4]   nitpick[satisfy, card ag=3, card i=4]
  oops

(*
lemma "\<forall>w v. ( ((\<^bold>\<diamond>U(\<^bold>B a \<phi>)) w) \<longrightarrow> ((\<^bold>\<diamond>U(\<^bold>B a \<phi>)) v) )" 
  by (simp add: mboxU_def mneg_def)
*)

(* Observation 1 - only with universal modality *)
lemma obs1:"\<forall>w a \<phi>. ( ((\<^bold>\<diamond>(\<^bold>B a \<phi>)) w) \<longrightarrow> (\<forall>v b. (a\<noteq>b) \<longrightarrow> ( (\<^bold>O[b\<rightarrow>a](\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a \<phi>))) v)) )"
  unfolding mbox_def mneg_def mobl_def mstit_def 
  (* using Reflexive_n mbox_def mneg_def mobl_def mstit_def by auto *)
  oops

(* Observation 2 - only with universal modality  *) 
lemma "(\<forall>w::i. \<forall>a::ag.  ((ag_n a) w) (\<lambda>w. True)) \<longrightarrow>
       (\<forall>w::i. \<forall>a::ag. \<forall>\<phi>. (\<forall>b. (a\<noteq>b) \<longrightarrow> ((\<^bold>O[b\<rightarrow>a](\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a \<phi>))) w)) \<longrightarrow> ((\<^bold>\<diamond>(\<^bold>B a \<phi>)) w)  )"
  unfolding LFT_Defs
  apply simp
  (* nitpick[card ag = 2, eval="(\<forall>w::i. \<forall>a::ag. \<forall>\<phi>. (\<forall>b. (a\<noteq>b) \<longrightarrow> ((\<^bold>O[b\<rightarrow>a](\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a \<phi>))) w)) \<longrightarrow> ((\<^bold>\<diamond>(\<^bold>B a \<phi>)) w)  )"] *)
  oops


(* checking that syntactic-semantic conditions correpond *)
(* lemma "\<forall>w::i. (\<forall>a \<phi>.  (((\<^bold>\<box> \<phi>)\<^bold>\<rightarrow>(\<^bold>E a \<phi>))w)) \<longrightarrow> (\<forall>a.  (((ag_n a) w) (\<lambda>w. True)))"  *)
lemma "\<forall>w::i. (\<forall>a.  (((\<^bold>E a \<^bold>\<top> ))w)) \<longrightarrow> (\<forall>a.  (((ag_n a) w) (\<lambda>w. True)))" 
  unfolding  LFT_Defs
  by simp

(* lemma "\<forall>w::i. (\<forall>a.  (((ag_n a) w) (\<lambda>w. True))) \<longrightarrow> ( \<forall>a \<phi>. (((\<^bold>\<box> \<phi>)\<^bold>\<rightarrow>(\<^bold>E a \<phi>))w))" *)
lemma "\<forall>w::i. (\<forall>a.  (((ag_n a) w) (\<lambda>w. True))) \<longrightarrow> ( \<forall>a \<phi>. (((\<^bold>E a \<^bold>\<top>))w))"
  unfolding  LFT_Defs
  by simp

(* iff *)
(* lemma "\<forall>w::i. (\<forall>a \<phi>.  (((\<^bold>\<box> \<phi>)\<^bold>\<rightarrow>(\<^bold>E a \<phi>))w)) \<longleftrightarrow> (\<forall>a.  (((ag_n a) w) (\<lambda>w. True)))"  *)
lemma "\<forall>w::i. (\<forall>a.  (((\<^bold>E a \<^bold>\<top> ))w)) \<longleftrightarrow> (\<forall>a.  (((ag_n a) w) (\<lambda>w. True)))" 
  unfolding  LFT_Defs
  by simp

  
(* 4.2.3 Immunity *)
(* found model, countermodel *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> 
      \<lfloor>\<^bold>\<not>\<^bold>\<diamond>(
      (\<^bold>E b (\<^bold>\<not> (((\<^bold>P[a\<rightarrow>b](\<^bold>B a \<phi>)) \<^bold>\<and> (\<^bold>P[a\<rightarrow>b](\<^bold>B a \<^bold>\<not>\<phi>)) \<^bold>\<and> (\<^bold>P[a\<rightarrow>b]((<\<^bold>B a> \<phi>) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<phi>) )) )) ))
      \<^bold>\<or>
      (\<^bold>E b \<^bold>\<not> (
       \<^bold>O[b\<rightarrow>a](
            (\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a \<phi>)) \<^bold>\<and>
            (\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a \<^bold>\<not>\<phi>)) \<^bold>\<and>
            (\<^bold>\<not> \<^bold>E b \<^bold>\<not>\<^bold>\<diamond>((<\<^bold>B a> \<phi>) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<phi>) )) )
      ))
      ) \<rfloor> )"
  nitpick[card ag=3, card i=4]   nitpick[satisfy, card ag=3, card i=4]
 (* Nitpick found a counterexample, a model *)
  oops


end