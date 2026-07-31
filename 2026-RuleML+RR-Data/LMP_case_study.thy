(* 
Luca Pasetto, Christoph Benzmüller, and Réka Markovich. 2026.
Right on Thought, Left Private: Reasoning about Mental Privacy in LogiKEy.
*)

section \<open>Right to Mental Privacy in HOL: Case Study\<close>

theory LMP_case_study
  imports LMP_DSL
begin

nitpick_params[user_axioms=true,assms=true,expect=genuine,show_all,format=2,mono=false,dont_box]

text \<open>A simple consistency check to begin.\<close>
lemma True nitpick[satisfy, card ag=2, card i=2] oops

consts a :: ag  c :: ag
consts p :: \<sigma>   q :: \<sigma>   r :: \<sigma>
consts w0 :: i  w1 :: i  w2 :: i

abbreviation (input) theta :: \<sigma> where
  "theta \<equiv> ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar)"

abbreviation (input) T_a :: "ag\<Rightarrow>bool" where
  "T_a \<equiv> \<lambda>x. x=c"

abbreviation (input) assumption_diff_ags where
  "assumption_diff_ags \<equiv> a \<noteq> c"

abbreviation (input) assumption_diff_worlds where
   "assumption_diff_worlds \<equiv> w0 \<noteq> w1 \<and> w0 \<noteq> w2 \<and> w1 \<noteq> w2"

text \<open>Propositional valuation.\<close>
abbreviation (input) assumption_lits where
  "assumption_lits \<equiv>
     (p w0 \<and> p w1) \<and>
     (\<not> q w0 \<and> q w1) \<and>
     (\<not> r w0 \<and> \<not> r w1)"

text \<open>Belief assumptions.\<close>
abbreviation (input) assumption_B where
  "assumption_B \<equiv>
     \<lfloor>\<^bold>B a \<^sup>Ap\<rfloor>w0 \<and>
     \<lfloor>\<^bold>B a theta\<rfloor>w0 \<and>
     \<lfloor>(<\<^bold>B a> \<^sup>Aq) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not> \<^sup>Aq))\<rfloor>w0 \<and>
     \<lfloor>(<\<^bold>B a> \<^sup>Ar) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not> \<^sup>Ar))\<rfloor>w0 \<and>
     \<lfloor>\<^bold>B a \<^sup>Ap\<rfloor>w1 \<and>
     \<lfloor>\<^bold>B a theta\<rfloor>w1"

text \<open>Knowledge assumptions.\<close>
abbreviation (input) assumption_K where
  "assumption_K \<equiv>
     \<lfloor>\<^bold>\<not> (\<^bold>K c (\<^bold>B a \<^sup>Ap))\<rfloor>w0 \<and>
     \<lfloor>\<^bold>\<not> (\<^bold>K c (\<^bold>B a theta))\<rfloor>w0 \<and>
     \<lfloor>\<^bold>K c (\<^bold>B a \<^sup>Ap)\<rfloor>w1 \<and>
     \<lfloor>\<^bold>K c (\<^bold>B a theta)\<rfloor>w1"

text \<open>
  Alice's direct freedom-of-thought protection on r, expressed with the DSL.
  We assume both the claim-right instance and the factual no-direct-interference
  condition at the two designated worlds.
\<close>
abbreviation (input) assumption_fot where
  "assumption_fot \<equiv> 
     \<lfloor>FoT a (\<^sup>Ar) T_a\<rfloor>w0 \<and>
     \<lfloor>FoT a (\<^sup>Ar) T_a\<rfloor>w1 \<and>
     \<lfloor>NoDirFoT c a (\<^sup>Ar)\<rfloor>w0 \<and>
     \<lfloor>NoDirFoT c a (\<^sup>Ar)\<rfloor>w1"

text \<open>
  L2.0 world-knowledge assumption: if Cerebra knows Alice's belief in p and in
  theta, then Cerebra removes Alice's non-belief attitudes with respect to q.
\<close>
abbreviation (input) q_steering :: \<sigma> where
  "q_steering \<equiv>
     (\<^bold>E c (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>B a (\<^bold>\<not> \<^sup>Aq))))) \<^bold>\<and>
     (\<^bold>E c (\<^bold>\<not> (\<^bold>\<diamond> ((<\<^bold>B a> \<^sup>Aq) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not> \<^sup>Aq))))))"

abbreviation (input) assumption_knowledge_enables_influence where
  "assumption_knowledge_enables_influence \<equiv>
     \<lfloor>((\<^bold>K c (\<^bold>B a \<^sup>Ap)) \<^bold>\<and> (\<^bold>K c (\<^bold>B a theta))) \<^bold>\<rightarrow> q_steering\<rfloor>w0 \<and>
     \<lfloor>((\<^bold>K c (\<^bold>B a \<^sup>Ap)) \<^bold>\<and> (\<^bold>K c (\<^bold>B a theta))) \<^bold>\<rightarrow> q_steering\<rfloor>w1"

text \<open>Complete set of case-study assumptions.\<close>
abbreviation (input) model_assumptions where
  "model_assumptions \<equiv>
     assumption_diff_ags \<and> assumption_diff_worlds \<and>
     assumption_lits \<and> assumption_B \<and> assumption_K \<and>
     assumption_fot \<and> assumption_knowledge_enables_influence"

subsection \<open>Automated reasoning results\<close>

text \<open>Consistency: Nitpick reports a model.\<close>
lemma model_assumptions_consistent: model_assumptions
  nitpick[satisfy]
  oops

text \<open>Mental-privacy access failures at w1, expressed with the DSL.\<close>
lemma MPLeak_p_w1:
  "model_assumptions \<longrightarrow> \<lfloor>MPLeakB a c (\<^sup>Ap)\<rfloor>w1"
  unfolding MPLeakB_def CtrlB_def
  by (metis AxiomS5_box Reflexive_n mbox_def mneg_def mstit_def symmetric_def)

lemma MPLeak_theta_w1:
  "model_assumptions \<longrightarrow> \<lfloor>MPLeakB a c theta\<rfloor>w1"
  unfolding MPLeakB_def CtrlB_def
  by (metis AxiomS5_box Reflexive_n mbox_def mneg_def mstit_def symmetric_def)

text \<open>The analogous is not entailed at w0 ; Nitpick finds countermodels.\<close>
lemma MPLeak_p_w0_not_entailed:
  "model_assumptions \<longrightarrow> \<lfloor>MPLeakB a c (\<^sup>Ap)\<rfloor>w0"
  nitpick
  oops

lemma MPLeak_theta_w0_not_entailed:
  "model_assumptions \<longrightarrow> \<lfloor>MPLeakB a c theta\<rfloor>w0"
  nitpick
  oops

text \<open>
  If the corresponding mental-privacy right is in force, the violation
  check follows from the leak.
\<close>
lemma MPViol_p_conditional_w1:
  "model_assumptions \<longrightarrow>
     \<lfloor>(MPB c a (\<^sup>Ap) T_a) \<^bold>\<rightarrow> (MPViolB c a (\<^sup>Ap) T_a)\<rfloor>w1"
  unfolding LMP_DSL_Defs
  using MPLeak_p_w1 
  by (smt (verit) AxiomS5_box Reflexive_n symmetric_def)

lemma MPViol_theta_conditional_w1:
  "model_assumptions \<longrightarrow>
     \<lfloor>(MPB c a theta T_a) \<^bold>\<rightarrow> (MPViolB c a theta T_a)\<rfloor>w1"
  unfolding LMP_DSL_Defs
  using MPLeak_theta_w1 
  by (smt (verit) AxiomS5_box Reflexive_n symmetric_def)

text \<open>Direct interference with q.\<close>
lemma DirFoT_q_w1:
  "model_assumptions \<longrightarrow> \<lfloor>DirFoT c a (\<^sup>Aq)\<rfloor>w1"
  unfolding LMP_DSL_Defs
  by blast

lemma DirFoT_q_w0_not_entailed:
  "model_assumptions \<longrightarrow> \<lfloor>DirFoT c a (\<^sup>Aq)\<rfloor>w0"
  nitpick
  oops

text \<open>At w1, the steering on q forces Alice into belief in q.\<close>
lemma q_steering_forces_box_Bq:
  "\<lfloor>q_steering\<rfloor>w1 \<longrightarrow> \<lfloor>\<^bold>\<box>(\<^bold>B a \<^sup>Aq)\<rfloor>w1"
  unfolding LMP_DSL_Defs
  using Reflexive_n by blast

lemma q_steering_forces_Bq:
  "\<lfloor>q_steering\<rfloor>w1 \<longrightarrow> \<lfloor>\<^bold>B a \<^sup>Aq\<rfloor>w1"
  unfolding LMP_DSL_Defs
  (* by (metis AxiomS5_box Reflexive_n reflexive_def) *)
  using AxiomS5_box Reflexive_n reflexive_def[of rbox] by blast

lemma Baq_w1:
  "model_assumptions \<longrightarrow> \<lfloor>\<^bold>B a \<^sup>Aq\<rfloor>w1"
  unfolding LMP_DSL_Defs 
  by (smt (verit) AxiomS5_box Reflexive_n reflexive_def)

text \<open>Belief closure: derive Ba r from Ba p, Ba q, and Ba(theta).\<close>
lemma belief_closure:
  "\<lfloor>((\<^bold>B a \<^sup>Ap) \<^bold>\<and> (\<^bold>B a \<^sup>Aq) \<^bold>\<and> (\<^bold>B a theta)) \<^bold>\<rightarrow> (\<^bold>B a \<^sup>Ar)\<rfloor>w1"
  by (simp add: mand_def mbel_def mimp_def)

lemma Bar_w1:
  "model_assumptions \<longrightarrow> \<lfloor>\<^bold>B a \<^sup>Ar\<rfloor>w1"
  unfolding LMP_DSL_Defs
  by (smt (verit) AxiomS5_box Reflexive_n reflexive_def)

text \<open>Freedom-of-thought checks for r and q.\<close>
lemma NoDirFoT_r_w1:
  "model_assumptions \<longrightarrow> \<lfloor>NoDirFoT c a (\<^sup>Ar)\<rfloor>w1"
  by simp

text \<open>FoT violation on r is not entailed.\<close>
lemma FoTViol_r_w1_not_entailed:
  "model_assumptions \<longrightarrow> \<lfloor>FoTViol a (\<^sup>Ar) T_a\<rfloor>w1"
  nitpick
  oops

text \<open>
  In fact, under the present assumptions the negation of the violation check for
  r follows, because NoDirFoT on r is assumed at w1.
\<close>
lemma not_FoTViol_r_w1:
  "model_assumptions \<longrightarrow> \<lfloor>\<^bold>\<not> (FoTViol a (\<^sup>Ar) T_a)\<rfloor>w1"
  unfolding LMP_DSL_Defs
  by simp

text \<open>If q were protected by FoT, the interference would trigger the violation check.\<close>
lemma FoTViol_q_conditional_w1:
  "model_assumptions \<longrightarrow>
     \<lfloor>(FoT a (\<^sup>Aq) T_a) \<^bold>\<rightarrow> (FoTViol a (\<^sup>Aq) T_a)\<rfloor>w1"
  unfolding LMP_DSL_Defs
  by auto

subsection \<open>Auxiliary sanity checks\<close>

text \<open>Knowledge of a belief implies failure of the corresponding CtrlB condition.\<close>
lemma KB_implies_not_CtrlB:
  "\<lfloor>(\<^bold>K c (\<^bold>B a \<phi>)) \<^bold>\<rightarrow> (MPLeakB a c \<phi>)\<rfloor>w1"
  unfolding MPLeakB_def CtrlB_def
  by (metis (full_types) AxiomS5_box Reflexive_n mbox_def mimp_def mneg_def mstit_def symmetric_def)

text \<open>The converse is not valid in general; Nitpick finds a countermodel.\<close>
lemma not_CtrlB_does_not_imply_KB:
  "\<lfloor>(MPLeakB a c \<phi>) \<^bold>\<rightarrow> (\<^bold>K c (\<^bold>B a \<phi>))\<rfloor>w1"
  nitpick
  oops

subsection \<open>Nitpick model\<close>

text \<open>Extra constraints used only to obtain a nice Nitpick model.\<close>
abbreviation (input) extra_assumptions where
  "extra_assumptions \<equiv>
     (\<forall>x y. (ag_b c x y \<longleftrightarrow> x=y) \<and> ag_k a x y
        \<and> (\<forall>a1 a2. ag_o a1 a2 x y \<longleftrightarrow> y=w2)) \<and>
     (\<forall>a1 a2 a3 a4. ag_o a1 a2 = ag_o a3 a4) \<and> (p w2 \<and> q w2 \<and> r w2)"

lemma readable_model:
  "model_assumptions \<and> extra_assumptions"
  unfolding LMP_DSL_Defs
  apply simp
  nitpick[satisfy, card ag = 2, card i = 4]
  oops

end
