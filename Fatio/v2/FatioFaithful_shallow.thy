section\<open>Shallow embedding of the BD logic (maximal)\<close>

theory FatioFaithful_shallow
  imports FatioFaithful_deep
begin

\<comment>\<open>Shallow embedding of the content logic: truth sets parametric in the valuation\<close>
type_synonym \<sigma>\<^sub>c = "\<V>\<Rightarrow>\<w>\<Rightarrow>bool"

definition AtmCS::"\<S>\<Rightarrow>\<sigma>\<^sub>c" ("_\<^sup>c\<^sup>s" [1000] 999) where "x\<^sup>c\<^sup>s \<equiv> \<lambda>V w. V x w"
definition NegCS::"\<sigma>\<^sub>c\<Rightarrow>\<sigma>\<^sub>c" ("\<not>\<^sup>c\<^sup>s_" [96] 96) where "\<not>\<^sup>c\<^sup>s\<phi> \<equiv> \<lambda>V w. \<not> \<phi> V w"
definition ImpCS::"\<sigma>\<^sub>c\<Rightarrow>\<sigma>\<^sub>c\<Rightarrow>\<sigma>\<^sub>c" (infixr "\<supset>\<^sup>c\<^sup>s" 93) where
  "\<phi> \<supset>\<^sup>c\<^sup>s \<psi> \<equiv> \<lambda>V w. \<phi> V w \<longrightarrow> \<psi> V w"
definition ValCS ("\<Turnstile>\<^sup>c\<^sup>s _") where "\<Turnstile>\<^sup>c\<^sup>s \<phi> \<equiv> \<forall>V w. \<phi> V w"

type_synonym \<sigma> = "\<W>\<Rightarrow>\<R>\<Rightarrow>\<R>\<Rightarrow>\<V>\<Rightarrow>\<U>\<Rightarrow>\<E>\<Rightarrow>\<w>\<Rightarrow>bool"

definition AtmS::"\<S>\<Rightarrow>\<sigma>" ("_\<^sup>s" [1000] 999) where "x\<^sup>s \<equiv> \<lambda>W B D V U E w. V x w"
definition DoneS::"FatioL\<Rightarrow>\<sigma>" ("Done\<^sup>s") where "Done\<^sup>s l \<equiv> \<lambda>W B D V U E w. U l w"
definition EntS::"Formula\<Rightarrow>Sign\<Rightarrow>Formula\<Rightarrow>\<sigma>" where "EntS \<Phi> sg \<phi> \<equiv> \<lambda>W B D V U E w. E \<Phi> sg \<phi> w"
definition ExJS::"Speaker\<Rightarrow>Sign\<Rightarrow>Formula\<Rightarrow>\<sigma>" where
  "ExJS i sg \<phi> \<equiv> \<lambda>W B D V U E w. \<exists>\<Delta>. U (Justify i \<Delta> sg \<phi>) w"
definition NegS::"\<sigma>\<Rightarrow>\<sigma>" ("\<not>\<^sup>s_" [96] 96) where "\<not>\<^sup>s\<phi> \<equiv> \<lambda>W B D V U E w. \<not> \<phi> W B D V U E w"
definition ImpS::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<supset>\<^sup>s" 93) where
  "\<phi> \<supset>\<^sup>s \<psi> \<equiv> \<lambda>W B D V U E w. \<phi> W B D V U E w \<longrightarrow> \<psi> W B D V U E w"
definition BelS::"Speaker\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<B>\<^sup>s") where
  "\<B>\<^sup>s i \<phi> \<equiv> \<lambda>W B D V U E w. \<forall>v:W. B i w v \<longrightarrow> \<phi> W B D V U E v"
definition DesS::"Speaker\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<D>\<^sup>s") where
  "\<D>\<^sup>s i \<phi> \<equiv> \<lambda>W B D V U E w. \<forall>v:W. D i w v \<longrightarrow> \<phi> W B D V U E v"

definition RelTS::"\<W>\<Rightarrow>\<R>\<Rightarrow>\<R>\<Rightarrow>\<V>\<Rightarrow>\<U>\<Rightarrow>\<E>\<Rightarrow>\<w>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("\<langle>_,_,_,_,_,_\<rangle>,_ \<Turnstile>\<^sup>s _") where
  "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<equiv> \<phi> W B D V U E w"
definition ValS ("\<Turnstile>\<^sup>s _") where "\<Turnstile>\<^sup>s \<phi> \<equiv> \<forall>W B D V U E. \<forall>w:W. \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>s \<phi>"

named_theorems DefS
declare AtmS_def[DefS,simp] DoneS_def[DefS,simp] EntS_def[DefS,simp] ExJS_def[DefS,simp]
  NegS_def[DefS,simp] ImpS_def[DefS,simp] BelS_def[DefS,simp] DesS_def[DefS,simp]
  RelTS_def[DefS,simp] ValS_def[DefS] AtmCS_def[DefS,simp] NegCS_def[DefS,simp]
  ImpCS_def[DefS,simp] ValCS_def[DefS]

end
