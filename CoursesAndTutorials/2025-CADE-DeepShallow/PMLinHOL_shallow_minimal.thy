theory PMLinHOL_shallow_minimal  imports PMLinHOL_preliminaries                         (* Christoph Benzmüller, 2025 *) 
begin            
\<comment>\<open>The acessibility relation R and the valuation function V are introduced as constants at the meta-level HOL\<close>
  consts R::\<R> V::\<V>  
\<comment>\<open>Shallow embedding (of propositional modal logic in HOL)\<close>
  type_synonym \<sigma> = "\<w>\<Rightarrow>bool"   
  definition AtmM::"\<S>\<Rightarrow>\<sigma>"      ("_\<^sup>m")                   where           "a\<^sup>m \<equiv> \<lambda>w. V a w"
  definition NegM::"\<sigma>\<Rightarrow>\<sigma>"      ("\<not>\<^sup>m")                   where       "\<not>\<^sup>m \<phi> \<equiv> \<lambda>w.  \<not>\<phi> w"
  definition ImpM::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<supset>\<^sup>m" 93)  where    "\<phi> \<supset>\<^sup>m \<psi> \<equiv> \<lambda>w. \<phi> w \<longrightarrow> \<psi> w"
  definition BoxM::"\<sigma>\<Rightarrow>\<sigma>"      ("\<box>\<^sup>m")                   where       "\<box>\<^sup>m \<phi> \<equiv> \<lambda>w. \<forall>v. R w v \<longrightarrow> \<phi> v" 
\<comment>\<open>Further logical connectives as definitions\<close>
  definition OrM      (infixr "\<or>\<^sup>m" 92)   where    "\<phi> \<or>\<^sup>m \<psi> \<equiv> \<not>\<^sup>m\<phi> \<supset>\<^sup>m \<psi>"
  definition AndM    (infixr "\<and>\<^sup>m" 95)  where     "\<phi> \<and>\<^sup>m \<psi> \<equiv> \<not>\<^sup>m(\<phi> \<supset>\<^sup>m \<not>\<^sup>m\<psi>)"
  definition DiaM     ("\<diamond>\<^sup>m_")                where         "\<diamond>\<^sup>m\<phi> \<equiv> \<not>\<^sup>m (\<box>\<^sup>m (\<not>\<^sup>m\<phi>)) "
  definition TopM    ("\<top>\<^sup>m")                  where           "\<top>\<^sup>m \<equiv> p\<^sup>m \<supset>\<^sup>m p\<^sup>m"
  definition BotM     ("\<bottom>\<^sup>m")                  where           "\<bottom>\<^sup>m \<equiv> \<not>\<^sup>m \<top>\<^sup>m"
\<comment>\<open>Definition of truth of a formula relative to a model \<open>\<langle>W,R,V\<rangle>\<close> and a possible world w\<close>
  definition RelativeTruthM :: "\<w>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("_  \<Turnstile>\<^sup>m _") where "w \<Turnstile>\<^sup>m \<phi> \<equiv> \<phi> w"
\<comment>\<open>Definition of validity\<close>
  definition  ValM ("\<Turnstile>\<^sup>m _") where "\<Turnstile>\<^sup>m \<phi>   \<equiv>  \<forall>w::\<w>. w \<Turnstile>\<^sup>m \<phi>"
\<comment>\<open>Collection of definitions in a bag called DefM\<close>
  named_theorems DefM declare AtmM_def[DefM,simp] NegM_def[DefM,simp] ImpM_def[DefM,simp] 
    BoxM_def[DefM,simp] OrM_def[DefM,simp] AndM_def[DefM,simp] DiaM_def[DefM,simp] TopM_def[DefM,simp] 
    BotM_def[DefM,simp] RelativeTruthM_def[DefM,simp] ValM_def[DefM,simp]
end


