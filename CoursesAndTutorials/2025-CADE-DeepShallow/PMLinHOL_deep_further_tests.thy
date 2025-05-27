theory PMLinHOL_deep_further_tests imports PMLinHOL_deep_tests                          (* Christoph Benzmüller, 2025 *)
begin             
\<comment>\<open>Implied modal principle\<close>
  lemma K_Dia: "\<Turnstile>\<^sup>d (\<box>\<^sup>d(\<phi> \<supset>\<^sup>d \<psi>)) \<supset>\<^sup>d ((\<diamond>\<^sup>d\<phi>) \<supset>\<^sup>d \<diamond>\<^sup>d\<psi>)"  by auto  
\<comment>\<open>Example 6.10 of Sider (2009) Logic for Philosophy\<close>
  lemma T1a:  "\<Turnstile>\<^sup>d \<box>\<^sup>dp\<^sup>d \<supset>\<^sup>d ((\<diamond>\<^sup>dq\<^sup>d) \<supset>\<^sup>d \<diamond>\<^sup>d (p\<^sup>d \<and>\<^sup>d q\<^sup>d))" by auto  \<comment>\<open>fast automation in meta-logic HOL\<close>
  lemma T1b: "\<Turnstile>\<^sup>d \<box>\<^sup>dp\<^sup>d \<supset>\<^sup>d ((\<diamond>\<^sup>dq\<^sup>d) \<supset>\<^sup>d \<diamond>\<^sup>d (p\<^sup>d \<and>\<^sup>d q\<^sup>d))"                         
    proof -                                                                       \<comment>\<open>alternative interactive proof in modal object logic K\<close>
      have 1: "\<Turnstile>\<^sup>d p\<^sup>d \<supset>\<^sup>d (q\<^sup>d \<supset>\<^sup>d (p\<^sup>d \<and>\<^sup>d q\<^sup>d))"              unfolding AndD_def using H1 H2 H3 MP  by metis
      have 2: "\<Turnstile>\<^sup>d \<box>\<^sup>d(p\<^sup>d \<supset>\<^sup>d (q\<^sup>d \<supset>\<^sup>d (p\<^sup>d \<and>\<^sup>d q\<^sup>d)))"                                           using 1 Nec              by metis
      have 3: "\<Turnstile>\<^sup>d \<box>\<^sup>dp\<^sup>d \<supset>\<^sup>d \<box>\<^sup>d(q\<^sup>d \<supset>\<^sup>d (p\<^sup>d \<and>\<^sup>d q\<^sup>d))"                                          using 2 Dist MP       by metis
      have 4: "\<Turnstile>\<^sup>d (\<box>\<^sup>d(q\<^sup>d \<supset>\<^sup>d (p\<^sup>d \<and>\<^sup>d q\<^sup>d))) \<supset>\<^sup>d ((\<diamond>\<^sup>dq\<^sup>d) \<supset>\<^sup>d \<diamond>\<^sup>d(p\<^sup>d \<and>\<^sup>d q\<^sup>d))"       using K_Dia              by metis
      have 5: "\<Turnstile>\<^sup>d \<box>\<^sup>dp\<^sup>d \<supset>\<^sup>d ((\<diamond>\<^sup>dq\<^sup>d) \<supset>\<^sup>d \<diamond>\<^sup>d (p\<^sup>d \<and>\<^sup>d q\<^sup>d))"                                  using 3 4 H1 H2 MP by metis 
      thus ?thesis . qed
end


