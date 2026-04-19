(* Luca Pasetto, Roberts Tarvids, Apostolos Tzimoulis and Christoph Benzmüller, 2026 *)
theory HP_axioms_test
  imports HP
begin

text \<open>HP axioms for the initial family F.\<close>

lemma equality [simp]:
  "(\<forall>v x x' Y b. x \<noteq> x' \<longrightarrow>
      (\<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b](v=\<^sup>h\<^sup>p\<^sup>px)) \<longrightarrow>
       \<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b](\<not>\<^sup>h\<^sup>p\<^sup>p(v=\<^sup>h\<^sup>p\<^sup>px')))))"
  by (simp add: AtomPhi_def Intervention_def NegationPhi_def Truth_def)

lemma definiteness [simp]:
  "\<forall>v Y b. V v \<longrightarrow> (\<exists>i. R v i \<and> \<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b](v=\<^sup>h\<^sup>p\<^sup>pi)))" 
  by (simp add: AtomPhi_def Intervention_def Truth_def)

lemma composition [simp]:
  "\<forall>v1 v2 i1 i2 Y b.
      ((V v1 \<and> V v2) \<and>
       \<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b](v1=\<^sup>h\<^sup>p\<^sup>pi1)) \<and>
       \<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b](v2=\<^sup>h\<^sup>p\<^sup>pi2)))
      \<longrightarrow>
      \<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([(fun_upd Y v1 True)\<leftarrow>(fun_upd b v1 i1)](v2=\<^sup>h\<^sup>p\<^sup>pi2))"
  by (smt (verit) AtomPhi_def Intervention_def Truth_def cv_reachable_fix fix_agree_endo fix_strengthen_intervention reachable_update_F)

lemma effectiveness:
  "\<forall>v i Y. (V v \<and> R v i) \<longrightarrow>
      \<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([(fun_upd Y v True)\<leftarrow>(fun_upd tx v i)](v=\<^sup>h\<^sup>p\<^sup>pi))"
  by (simp add: AtomPhi_def Intervention_def Truth_def reachable_base)

lemma effectiveness_single:
  "\<forall>v i. (V v \<and> R v i) \<longrightarrow>
      \<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([(\<lambda>x. x = v)\<leftarrow>(fun_upd tx v i)](v=\<^sup>h\<^sup>p\<^sup>pi))"
  by (simp add: AtomPhi_def Intervention_def Truth_def cv_intervention_hit reachable_base)

lemma C5_recursiveness:
  "\<forall>X0 Xk.
      Xk \<noteq> X0 \<longrightarrow>
      ((U X0 \<and> V Xk) \<or> (V X0 \<and> V Xk \<and> find_index ord X0 < find_index ord Xk)) \<longrightarrow>
      \<not> ((U Xk \<and> V X0) \<or> (V Xk \<and> V X0 \<and> find_index ord Xk < find_index ord X0))"
  using recur_ord by blast

lemma recursiveness_direct:
  "\<forall>X0 Xk.
      Xk \<noteq> X0 \<longrightarrow>
      ((directly_causes F X0 Xk) \<longrightarrow> \<not> (directly_causes F Xk X0))"
  by (metis directly_causes_def exo_no_direct_dep order_less_imp_not_less topo_ord)

lemma determinism_neg_lit:
  "\<forall>v i Y b.
      (\<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b](\<not>\<^sup>h\<^sup>p\<^sup>p(v=\<^sup>h\<^sup>p\<^sup>pi))))
      \<longleftrightarrow>
      (\<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p (\<not>\<^sup>h\<^sup>p\<^sup>p([Y\<leftarrow>b](v=\<^sup>h\<^sup>p\<^sup>pi))))"
  by (simp add: Intervention_def NegationPhi_def)

lemma determinism_neg:
  "\<forall>Y b \<phi>.
      (\<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b](\<not>\<^sup>h\<^sup>p\<^sup>p \<phi>)))
      \<longleftrightarrow>
      (\<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p (\<not>\<^sup>h\<^sup>p\<^sup>p([Y\<leftarrow>b](\<phi>))))"
  by (simp add: Intervention_def NegationPhi_def)

lemma determinism_conj_lit:
  "\<forall>v1 v2 i1 i2 Y b.
      (\<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b]((v1=\<^sup>h\<^sup>p\<^sup>pi1) \<and>\<^sup>h\<^sup>p\<^sup>p (v2=\<^sup>h\<^sup>p\<^sup>pi2))))
      \<longleftrightarrow>
      (\<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p (([Y\<leftarrow>b](v1=\<^sup>h\<^sup>p\<^sup>pi1)) \<and>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b](v2=\<^sup>h\<^sup>p\<^sup>pi2))))"
  using ConjunctionPhi_def Intervention_def by auto

lemma determinism_conj:
  "\<forall>Y b \<phi> \<psi>.
      (\<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b](\<phi> \<and>\<^sup>h\<^sup>p\<^sup>p \<psi>)))
      \<longleftrightarrow>
      (\<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p (([Y\<leftarrow>b]\<phi>) \<and>\<^sup>h\<^sup>p\<^sup>p ([Y\<leftarrow>b]\<psi>)))"
  using ConjunctionPhi_def Intervention_def by auto

lemma MP:
  "\<forall>\<phi> \<psi>. (\<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p \<phi> \<and> \<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p (\<phi> \<rightarrow>\<^sup>h\<^sup>p\<^sup>p \<psi>)) \<longrightarrow> \<langle>F\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p \<psi>"
  by (simp add: ImplicationPhi_def Truth_def)

end
