(* Sebastian Reiche and Christoph Benzmüller, 2021 *)
theory PAL_experiments imports PAL_definitions

begin
 (* Parameter settings *)
 nitpick_params[user_axioms=true, format=4, show_all]
 declare [[smt_solver=cvc4,smt_oracle]]

 (*Some useful lemmata *) 
 lemma trans_tc: "transitive (tc R)" unfolding Defs by metis
 lemma trans_inv_tc: "transitive (inverse_rel (tc R))" unfolding Defs by metis
 lemma sub_rel_tc: "symmetric R \<longrightarrow> (sub_rel R (inverse_rel (tc R)))" unfolding Defs by smt
 lemma sub_rel_tc_tc: "symmetric R \<longrightarrow> (sub_rel (tc R) (inverse_rel (tc R)))" 
   using sub_rel_def sub_rel_tc tc_def trans_inv_tc by fastforce
 lemma symm_tc: "symmetric R \<longrightarrow> symmetric (tc R)"  
   using inverse_rel_def sub_rel_def sub_rel_tc_tc symmetric_def by auto

 (* System K: is implied by the semantical embedding *)
 lemma tautologies: "\<^bold>\<lfloor>\<^bold>\<top>\<^bold>\<rfloor>" by auto
 lemma axiom_K: "\<A> i \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>i (\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> ((\<^bold>K\<^sub>i \<phi>) \<^bold>\<rightarrow> (\<^bold>K\<^sub>i \<psi>))\<^bold>\<rfloor>" by auto 
 lemma modusponens: assumes 1: "\<^bold>\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<^bold>\<rfloor>" and 2: "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor>" shows "\<^bold>\<lfloor>\<psi>\<^bold>\<rfloor>" using 1 2 by auto  
 lemma necessitation: assumes 1: "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor>" shows "\<A> i \<Longrightarrow> \<^bold>\<lfloor>\<^bold>K\<^sub>i \<phi>\<^bold>\<rfloor>" using 1 by auto
 (* More axioms: implied by the semantical embedding  *)
 lemma axiom_T: "reflexive i \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>i \<phi>) \<^bold>\<rightarrow> \<phi>\<^bold>\<rfloor>" using reflexive_def by auto 
 lemma axiom_4: "transitive i \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>i \<phi>) \<^bold>\<rightarrow> (\<^bold>K\<^sub>i (\<^bold>K\<^sub>i \<phi>))\<^bold>\<rfloor>" using transitive_def by meson 
 lemma axiom_5: "euclidean i \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>\<not>\<^bold>K\<^sub>i \<phi>) \<^bold>\<rightarrow> (\<^bold>K\<^sub>i (\<^bold>\<not>\<^bold>K\<^sub>i \<phi>))\<^bold>\<rfloor>" using euclidean_def by meson 
 (*Reduction axioms: implied by the semantical embedding *)
 lemma atomic_permanence: "\<^bold>\<lfloor>(\<^bold>[\<^bold>!\<phi>\<^bold>]\<^sup>Ap) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<rightarrow> \<^sup>Ap)\<^bold>\<rfloor>" by auto
 lemma conjunction: "\<^bold>\<lfloor>(\<^bold>[\<^bold>!\<phi>\<^bold>](\<psi> \<^bold>\<and> \<chi>)) \<^bold>\<rightarrow> ((\<^bold>[\<^bold>!\<phi>\<^bold>]\<psi>) \<^bold>\<and> (\<^bold>[\<^bold>!\<phi>\<^bold>]\<chi>))\<^bold>\<rfloor>" by auto
 lemma part_func: "\<^bold>\<lfloor>(\<^bold>[\<^bold>!\<phi>\<^bold>]\<^bold>\<not>\<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>]\<psi>))\<^bold>\<rfloor>" by auto
 lemma action_knowledge: "\<^bold>\<lfloor>(\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>K\<^sub>i \<psi>)) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<rightarrow> (\<^bold>K\<^sub>i (\<phi> \<^bold>\<rightarrow> (\<^bold>[\<^bold>!\<phi>\<^bold>]\<psi>))))\<^bold>\<rfloor>" by auto
 lemma "\<^bold>\<lfloor>(\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<psi>\<^bold>\<rparr>)) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<rightarrow> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<phi>\<^bold>\<and>(\<^bold>[\<^bold>!\<phi>\<^bold>]\<chi>)\<^bold>|\<^bold>[\<^bold>!\<phi>\<^bold>]\<psi>\<^bold>\<rparr>))\<^bold>\<rfloor>" 
   by (smt intersection_rel_def sub_rel_def tc_def transitive_def) (* takes long *)


 (* Axiom schemes for RCK: implied by the semantical embedding *)
 lemma \<C>_normality: "\<^bold>\<lfloor>\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rightarrow>\<psi>\<^bold>\<rparr> \<^bold>\<rightarrow>(\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr> \<^bold>\<rightarrow> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<psi>\<^bold>\<rparr>)\<^bold>\<rfloor>" unfolding Defs by blast

 lemma mix_axiom1: "\<^bold>\<lfloor>\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr> \<^bold>\<rightarrow> \<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<and> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)))\<^bold>\<rfloor>" unfolding Defs by smt

 lemma mix_axiom2': "A = (\<lambda>x. False) \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<and> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)))) \<^bold>\<rightarrow> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>\<^bold>\<rfloor>" 
   unfolding Defs by (metis (full_types)) 
 lemma mix_axiom2'': "A = (\<lambda>x. True) \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<and> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)))) \<^bold>\<rightarrow> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>\<^bold>\<rfloor>" 
   unfolding Defs by (metis (full_types)) (* takes long *)
 lemma mix_axiom2''': "A = (\<lambda>x. x = a) \<and> S5Agent a \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<and> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)))) \<^bold>\<rightarrow> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>\<^bold>\<rfloor>" 
   unfolding Defs (* sledgehammer finds proof, but reconstruction times✕out *) oops 
 lemma mix_axiom2'''':
   "A = (\<lambda>x. x = a \<or> x = b) \<and> S5Agent a  \<and> S5Agent b \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<and> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)))) \<^bold>\<rightarrow> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>\<^bold>\<rfloor>" 
   unfolding Defs (* sledgehammer and nitpick timeout *) oops
 lemma mix_axiom2_general: "\<^bold>\<lfloor>(\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<and> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)))) \<^bold>\<rightarrow> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>\<^bold>\<rfloor>"
   unfolding Defs  (* timeout *) oops

 lemma induction_axiom':
   "A = (\<lambda>x. False) \<Longrightarrow> \<^bold>\<lfloor>((\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>)) \<^bold>\<and> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi> \<^bold>\<rightarrow> (\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>))\<^bold>\<rparr>) \<^bold>\<rightarrow> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)\<^bold>\<rfloor>" 
   unfolding Defs by (metis (full_types)) 
 lemma induction_axiom'':
   "A = (\<lambda>x. True) \<Longrightarrow> \<^bold>\<lfloor>((\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>)) \<^bold>\<and> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi> \<^bold>\<rightarrow> (\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>))\<^bold>\<rparr>) \<^bold>\<rightarrow> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)\<^bold>\<rfloor>" 
   unfolding Defs (* sledgehammer finds proof, but reconstruction times✕out *) oops 
 lemma induction_axiom''':
   "A = (\<lambda>x. x = a)  \<and> S5Agent a  \<Longrightarrow> \<^bold>\<lfloor>((\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>)) \<^bold>\<and> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi> \<^bold>\<rightarrow> (\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>))\<^bold>\<rparr>) \<^bold>\<rightarrow> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)\<^bold>\<rfloor>" 
   unfolding Defs (* sledgehammer finds proof, but reconstruction times✕out *) oops 
 lemma induction_axiom'''':
   "A = (\<lambda>x. x = a \<or> x = b) \<and> S5Agent a  \<and> S5Agent b
         \<Longrightarrow> \<^bold>\<lfloor>((\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>)) \<^bold>\<and> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi> \<^bold>\<rightarrow> (\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>))\<^bold>\<rparr>) \<^bold>\<rightarrow> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)\<^bold>\<rfloor>" 
   unfolding Defs (* sledgehammer and nitpick timeout *) oops
 lemma induction_axiom_general: "\<^bold>\<lfloor>((\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>)) \<^bold>\<and> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi> \<^bold>\<rightarrow> (\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>))\<^bold>\<rparr>) \<^bold>\<rightarrow> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)\<^bold>\<rfloor>"
   unfolding Defs (* sledgehammer and nitpick timeout *) oops

 (* To ensure completeness we may also simply postulate axiom schemata in the LogiKEy approach *)
 axiomatization where 
  mix_axiom_general: "\<^bold>\<lfloor>\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr> \<^bold>\<rightarrow> \<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<and> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)))\<^bold>\<rfloor>" and
  induction_axiom_general: "\<^bold>\<lfloor>((\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>)) \<^bold>\<and> \<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi> \<^bold>\<rightarrow> (\<^bold>E\<^sub>A(\<chi> \<^bold>\<rightarrow> \<phi>))\<^bold>\<rparr>) \<^bold>\<rightarrow> (\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)\<^bold>\<rfloor>"

 (* Necessitation rules: implied by the semantical embedding *)
 lemma announcement_nec: assumes "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor>" shows "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<psi>\<^bold>]\<phi>\<^bold>\<rfloor>" by (simp add: assms)
 lemma rkc_necessitation: assumes "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor>" shows "\<^bold>\<lfloor>(\<^bold>C\<^sub>A\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)\<^bold>\<rfloor>"
   by (smt assms intersection_rel_def sub_rel_def tc_def transitive_def)

 (* Checking for consistency (again) *)
 lemma True nitpick[satisfy,user_axioms] oops (* model found *)
 lemma False sledgehammer oops (* provers time out, i.e. fail to prove falsity *)

 (* Further axioms: implied for atomic formulas, but not implied in general *)
 lemma "\<^bold>\<lfloor>\<^sup>Ap \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^bold>\<not>\<^sup>Ap)\<^bold>\<rfloor>" by simp
 lemma "\<^bold>\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>\<not>\<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)
 lemma "\<^bold>\<lfloor>\<^sup>Ap \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^bold>\<not>\<^bold>K\<^sub>a \<^sup>Ap)\<^bold>\<rfloor>" by simp
 lemma "\<^bold>\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>\<not>\<^bold>K\<^sub>a \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)  
 lemma "\<^bold>\<lfloor>\<^sup>Ap \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^bold>\<not>\<^bold>K\<^sub>r \<^sup>Ap)\<^bold>\<rfloor>" by simp
 lemma "\<^bold>\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>\<not>\<^bold>K\<^sub>r \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)  
 lemma "\<^bold>\<lfloor>\<^sup>Ap \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^sup>Ap \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>r \<^sup>Ap)\<^bold>\<rfloor>" by simp
 lemma "\<^bold>\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<phi> \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>r \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)  
 lemma "\<^bold>\<lfloor>(\<^sup>Ap \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>r \<^sup>Ap) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>r \<^sup>Ap\<^bold>](\<^sup>Ap \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>r \<^sup>Ap)\<^bold>\<rfloor>" by blast
 lemma "\<^bold>\<lfloor>(\<phi> \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>r \<phi>) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi> \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>r \<phi>\<^bold>](\<phi> \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>r \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)
 lemma "S5Agent r \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>r \<^sup>Ap) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^bold>\<not>\<^bold>K\<^sub>r \<^sup>Ap)\<^bold>\<rfloor>" using reflexive_def by auto
 lemma "S5Agent r \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>r \<phi>) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>\<not>\<^bold>K\<^sub>r \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)  
 lemma "S5Agent r \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>r \<^sup>Ap) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^sup>Ap \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>r \<^sup>Ap)\<^bold>\<rfloor>" using  reflexive_def by auto
 lemma "S5Agent r \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>r \<phi>) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<phi> \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>r \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)

 (* Further checks on the atomic versus general validity. *)
 lemma "\<^bold>\<lfloor>p \<^bold>\<leftrightarrow> q\<^bold>\<rfloor> \<Longrightarrow> \<forall>W v. (p W v \<longleftrightarrow> q W v)" unfolding Defs nitpick oops (* countermodel *)
 lemma "\<forall>W v. (p W v \<longleftrightarrow> q W v) \<Longrightarrow> \<^bold>\<lfloor>p \<^bold>\<leftrightarrow> q\<^bold>\<rfloor>" unfolding Defs by simp 
 lemma "\<^bold>\<lfloor>\<^sup>Ap \<^bold>\<leftrightarrow> \<^sup>Aq\<^bold>\<rfloor> \<Longrightarrow> \<forall>v. (p v \<longleftrightarrow> q v)" unfolding Defs by simp
 lemma "\<forall>v. (p v \<longleftrightarrow> q v) \<Longrightarrow> \<^bold>\<lfloor>\<^sup>Ap \<^bold>\<leftrightarrow> \<^sup>Aq\<^bold>\<rfloor>" unfolding Defs by simp

 (* Concrete models can be defined and studied. *)
 lemma assumes "W = (\<lambda>x. x = w1 \<or> x = w2 \<or> x = w3)"
               "w1 \<noteq> w2" "w1 \<noteq> w3" "w2 \<noteq> w3" 
               "p W w1" "p W w2" "\<not>(p W w3)"
               "a w1 w1" "a w1 w2" "a w2 w1" 
               "a w2 w2" "\<not>(a w1 w3)" "\<not>(a w3 w1)"
               "\<not>(a w2 w3)" "\<not>(a w3 w2)" "a w3 w3" 
               "b w1 w1" "\<not>(b w1 w2)" "\<not>(b w2 w1)"
               "b w2 w2" "\<not>(b w1 w3)" "\<not>(b w3 w1)"
               "b w2 w3" "b w3 w2" "b w3 w3" 
         shows "((p \<^bold>\<and> (\<^bold>K\<^sub>a p) \<^bold>\<and> (\<^bold>K\<^sub>b p)) \<^bold>\<and> \<^bold>\<not>(\<^bold>K\<^sub>a (\<^bold>K\<^sub>b p))) W w1" 
   unfolding Defs 
     nitpick[satisfy, atoms=w1 w2 w3] (* model *)
     using assms(1) assms(5) assms(6) assms(7)
           assms(9) assms(12) assms(21) assms(23) by blast (* proof *)
end