theory PMLinHOL_deep imports PMLinHOL_preliminaries                                            (* Christoph Benzmüller, 2025 *)       
begin                 
\<comment>\<open>Deep embedding (of propositional modal logic in HOL)\<close>
  datatype PML = AtmD \<S> ("_\<^sup>d") | NotD PML ("\<not>\<^sup>d") | ImpD PML PML (infixr "\<supset>\<^sup>d" 93) | BoxD PML ("\<box>\<^sup>d")
\<comment>\<open>Further logical connectives as definitions\<close>
  definition OrD      (infixr "\<or>\<^sup>d" 92)  where     "\<phi>\<or>\<^sup>d\<psi> \<equiv> \<not>\<^sup>d\<phi> \<supset>\<^sup>d \<psi>"
  definition AndD    (infixr "\<and>\<^sup>d" 95)  where     "\<phi>\<and>\<^sup>d\<psi> \<equiv> \<not>\<^sup>d(\<phi> \<supset>\<^sup>d \<not>\<^sup>d\<psi>)"
  definition DiaD     ("\<diamond>\<^sup>d_")                where       "\<diamond>\<^sup>d\<phi> \<equiv> \<not>\<^sup>d(\<box>\<^sup>d(\<not>\<^sup>d\<phi>)) "
  definition TopD    ("\<top>\<^sup>d")                  where        "\<top>\<^sup>d  \<equiv>  p\<^sup>d \<supset>\<^sup>d p\<^sup>d"
  definition BotD     ("\<bottom>\<^sup>d")                  where        "\<bottom>\<^sup>d  \<equiv> \<not>\<^sup>d \<top>\<^sup>d"
\<comment>\<open>Definition of truth of a formula relative to a model \<open>\<langle>W,R,V\<rangle>\<close> and a possible world w\<close>
  primrec RelativeTruthD :: "\<W>\<Rightarrow>\<R>\<Rightarrow>\<V> \<Rightarrow>\<w>\<Rightarrow>PML\<Rightarrow>bool" ("\<langle>_,_,_\<rangle>,_  \<Turnstile>\<^sup>d _") where
       "\<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d a\<^sup>d          = (V a w)"   
     | "\<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<not>\<^sup>d\<phi>       = (\<not> \<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<phi>)"
     | "\<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<psi>   = (\<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<phi>  \<longrightarrow>  \<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<psi>)"
     | "\<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi>       = (\<forall>v:W. R w v \<longrightarrow> \<langle>W,R,V\<rangle>, v \<Turnstile>\<^sup>d \<phi>)"
\<comment>\<open>Definition of validity\<close>
  definition ValD ("\<Turnstile>\<^sup>d _") where "(\<Turnstile>\<^sup>d \<phi>) \<equiv> (\<forall>W R V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi>)"
\<comment>\<open>Collection of definitions in a bag called DefD\<close>
  named_theorems DefD declare OrD_def[DefD,simp] AndD_def[DefD,simp] DiaD_def[DefD,simp] 
    TopD_def[DefD,simp] BotD_def[DefD,simp] RelativeTruthD_def[DefD,simp] ValD_def[DefD,simp]  
end

