section\<open>Shallow embedding of the BD logic (minimal)\<close>

theory FatioFaithful_shallow_minimal
  imports FatioFaithful_deep
begin

text\<open>The minimal shallow embedding fixes one model at the meta level: the
accessibility relations and valuations are uninterpreted HOL constants, formulas
are plain truth sets over worlds, and the world domain is implicitly the full type
\<open>\<w>\<close>. This is the classical SSE style of LogiKEy \<^cite>\<open>"LogiKEy2020"\<close> and the style of the
original HOMML/FATIO development; the price, made explicit by the faithfulness
theorems below, is that faithfulness holds relative to full-domain models only.\<close>

consts B\<^sub>0::\<R> D\<^sub>0::\<R> V\<^sub>0::\<V> U\<^sub>0::\<U> E\<^sub>0::\<E>

type_synonym \<sigma>\<^sub>m = "\<w>\<Rightarrow>bool"

definition AtmM::"\<S>\<Rightarrow>\<sigma>\<^sub>m" ("_\<^sup>m" [1000] 999) where "x\<^sup>m \<equiv> \<lambda>w. V\<^sub>0 x w"
definition DoneM::"FatioL\<Rightarrow>\<sigma>\<^sub>m" ("Done\<^sup>m") where "Done\<^sup>m l \<equiv> \<lambda>w. U\<^sub>0 l w"
definition EntM::"Formula\<Rightarrow>Sign\<Rightarrow>Formula\<Rightarrow>\<sigma>\<^sub>m" where "EntM \<Phi> sg \<phi> \<equiv> \<lambda>w. E\<^sub>0 \<Phi> sg \<phi> w"
definition ExJM::"Speaker\<Rightarrow>Sign\<Rightarrow>Formula\<Rightarrow>\<sigma>\<^sub>m" where
  "ExJM i sg \<phi> \<equiv> \<lambda>w. \<exists>\<Delta>. U\<^sub>0 (Justify i \<Delta> sg \<phi>) w"
definition NegM::"\<sigma>\<^sub>m\<Rightarrow>\<sigma>\<^sub>m" ("\<not>\<^sup>m_" [96] 96) where "\<not>\<^sup>m\<phi> \<equiv> \<lambda>w. \<not> \<phi> w"
definition ImpM::"\<sigma>\<^sub>m\<Rightarrow>\<sigma>\<^sub>m\<Rightarrow>\<sigma>\<^sub>m" (infixr "\<supset>\<^sup>m" 93) where "\<phi> \<supset>\<^sup>m \<psi> \<equiv> \<lambda>w. \<phi> w \<longrightarrow> \<psi> w"
definition BelM::"Speaker\<Rightarrow>\<sigma>\<^sub>m\<Rightarrow>\<sigma>\<^sub>m" ("\<B>\<^sup>m") where "\<B>\<^sup>m i \<phi> \<equiv> \<lambda>w. \<forall>v. B\<^sub>0 i w v \<longrightarrow> \<phi> v"
definition DesM::"Speaker\<Rightarrow>\<sigma>\<^sub>m\<Rightarrow>\<sigma>\<^sub>m" ("\<D>\<^sup>m") where "\<D>\<^sup>m i \<phi> \<equiv> \<lambda>w. \<forall>v. D\<^sub>0 i w v \<longrightarrow> \<phi> v"

definition RelTM::"\<w>\<Rightarrow>\<sigma>\<^sub>m\<Rightarrow>bool" ("_ \<Turnstile>\<^sup>m _") where "w \<Turnstile>\<^sup>m \<phi> \<equiv> \<phi> w"
definition ValM ("\<Turnstile>\<^sup>m _") where "\<Turnstile>\<^sup>m \<phi> \<equiv> \<forall>w. \<phi> w"

named_theorems DefM
declare AtmM_def[DefM,simp] DoneM_def[DefM,simp] EntM_def[DefM,simp] ExJM_def[DefM,simp]
  NegM_def[DefM,simp] ImpM_def[DefM,simp] BelM_def[DefM,simp] DesM_def[DefM,simp]
  RelTM_def[DefM,simp] ValM_def[DefM]

end
