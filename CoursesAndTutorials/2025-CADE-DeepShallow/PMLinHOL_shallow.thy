theory PMLinHOL_shallow imports PMLinHOL_preliminaries                                        (* Christoph Benzmüller, 2025 *)
begin                 
\<comment>\<open>Shallow embedding (of propositional modal logic in HOL)\<close>
  type_synonym \<sigma> = "\<W>\<Rightarrow>\<R>\<Rightarrow>\<V>\<Rightarrow>\<w>\<Rightarrow>bool"
  definition AtmS::"\<S>\<Rightarrow>\<sigma>"      ("_\<^sup>s")                   where          "a\<^sup>s \<equiv> \<lambda>W R V w. V a w"
  definition NegS::"\<sigma>\<Rightarrow>\<sigma>"      ("\<not>\<^sup>s")                   where      "\<not>\<^sup>s \<phi> \<equiv> \<lambda>W R V w.  \<not>(\<phi> W R V w)"
  definition ImpS::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<supset>\<^sup>s" 93)  where   "\<phi> \<supset>\<^sup>s \<psi> \<equiv> \<lambda>W R V w. (\<phi> W R V w) \<longrightarrow> (\<psi> W R V w)"
  definition BoxS::"\<sigma>\<Rightarrow>\<sigma>"      ("\<box>\<^sup>s")                   where      "\<box>\<^sup>s \<phi> \<equiv> \<lambda>W R V w. \<forall>v:W. R w v \<longrightarrow> (\<phi> W R V v)" 
\<comment>\<open>Further logical connectives as definitions\<close>
  definition OrS       (infixr "\<or>\<^sup>s" 92)  where      "\<phi> \<or>\<^sup>s \<psi> \<equiv> \<not>\<^sup>s\<phi> \<supset>\<^sup>s \<psi>"
  definition AndS    (infixr "\<and>\<^sup>s" 95)   where      "\<phi> \<and>\<^sup>s \<psi> \<equiv> \<not>\<^sup>s(\<phi> \<supset>\<^sup>s \<not>\<^sup>s\<psi>)"
  definition DiaS     ("\<diamond>\<^sup>s")                  where          "\<diamond>\<^sup>s\<phi> \<equiv> \<not>\<^sup>s (\<box>\<^sup>s (\<not>\<^sup>s\<phi>)) "
  definition TopS     ("\<top>\<^sup>s")                  where            "\<top>\<^sup>s \<equiv>  p\<^sup>s \<supset>\<^sup>s p\<^sup>s"
  definition BotS     ("\<bottom>\<^sup>s")                   where            "\<bottom>\<^sup>s \<equiv> \<not>\<^sup>s \<top>\<^sup>s"
\<comment>\<open>Definition of truth of a formula relative to a model \<open>\<langle>W,R,V\<rangle>\<close> and a possible world w\<close>
  definition RelativeTruthS :: "\<W>\<Rightarrow>\<R>\<Rightarrow>\<V> \<Rightarrow>\<w>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("\<langle>_,_,_\<rangle>,_  \<Turnstile>\<^sup>s _") where "\<langle>W,R,V\<rangle>,w  \<Turnstile>\<^sup>s \<phi> \<equiv> \<phi> W R V w"
\<comment>\<open>Definition of validity\<close>
  definition  ValS ("\<Turnstile>\<^sup>s _") where "\<Turnstile>\<^sup>s \<phi>  \<equiv>  \<forall>W R V. \<forall>w:W. \<langle>W,R,V\<rangle>,w  \<Turnstile>\<^sup>s \<phi>"
\<comment>\<open>Collection of definitions in a bag called DefS\<close>
  named_theorems DefS declare AtmS_def[DefS,simp] NegS_def[DefS,simp] ImpS_def[DefS,simp] 
    BoxS_def[DefS,simp] OrS_def[DefS,simp] AndS_def[DefS,simp] DiaS_def[DefS,simp] TopS_def[DefS,simp] 
    BotS_def[DefS,simp] RelativeTruthS_def[DefS,simp] ValS_def[DefS,simp]
end




