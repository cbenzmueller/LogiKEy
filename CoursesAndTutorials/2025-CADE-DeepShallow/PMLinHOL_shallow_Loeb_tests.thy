theory PMLinHOL_shallow_Loeb_tests imports PMLinHOL_shallow                                (* Christoph Benzmüller, 2025 *)
begin  
\<comment>\<open>Löb axiom: with the maximal shallow embedding automated reasoning tools are weakly responsive\<close>
  lemma Loeb1:   "\<forall>\<phi>. \<Turnstile>\<^sup>s \<box>\<^sup>s( \<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>" nitpick[card \<w>=1,card \<S>=1] oops \<comment>\<open>nitpick: Counterexample\<close>
  lemma Loeb2:   "(conversewf R \<and> transitive R) 
                                \<longrightarrow>  (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>)" \<comment>\<open>sledgehammer: Proof found\<close> oops
  lemma Loeb3:   "(conversewf R \<and> transitive R) 
                                \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>)" \<comment>\<open>sledgehammer: No Proof\<close> oops
  lemma Loeb3a: "conversewf R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>)" \<comment>\<open>sh: Proof found\<close> oops (**)
  lemma Loeb3b: "transitive R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>)" \<comment>\<open>sh: No Proof\<close> oops
  lemma Loeb3c: "irreflexive R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>)" \<comment>\<open>sh: Proof found\<close> oops
end

