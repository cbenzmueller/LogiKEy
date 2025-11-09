theory PMLinHOL_deep_Loeb_tests imports PMLinHOL_deep                                         (* Christoph Benzmüller, 2025 *)
begin  
\<comment>\<open>Löb axiom: with the deep embedding automated reasoning tools are not very responsive\<close>
  lemma Loeb1: "\<forall>\<phi>. \<Turnstile>\<^sup>d \<box>\<^sup>d( \<box>\<^sup>d\<phi> \<supset>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d\<phi>" nitpick[card \<w>=1,card \<S>=1] oops \<comment>\<open>nitpick: Counterexample\<close>
(**)  lemma Loeb2: "(conversewf R \<and> transitive R) 
                                \<longrightarrow>  (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi> \<supset>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d\<phi>)" \<comment>\<open>sledgehammer: No Proof\<close> oops
  lemma Loeb3: "(conversewf R \<and> transitive R) 
                                 \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi> \<supset>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d\<phi>)" \<comment>\<open>sledgehammer: No Proof\<close> oops
(**)  lemma Loeb3a: "conversewf R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi> \<supset>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d\<phi>)" \<comment>\<open>sh: No Proof\<close> oops
  lemma Loeb3b: "transitive R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi> \<supset>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d\<phi>)" \<comment>\<open>sh: No Proof\<close> oops
(**)  lemma Loeb3c: "irreflexive R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi> \<supset>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d\<phi>)" \<comment>\<open>sh: No Proof\<close> oops
end

 