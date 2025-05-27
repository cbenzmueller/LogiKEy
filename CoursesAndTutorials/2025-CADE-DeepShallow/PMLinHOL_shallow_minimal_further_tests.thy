theory PMLinHOL_shallow_minimal_further_tests imports PMLinHOL_shallow_minimal_tests                    (* C.B., 2025 *)
begin             
\<comment>\<open>Implied modal principle\<close>
  lemma K_Dia: "\<Turnstile>\<^sup>m (\<box>\<^sup>m(\<phi> \<supset>\<^sup>m \<psi>)) \<supset>\<^sup>m ((\<diamond>\<^sup>m\<phi>) \<supset>\<^sup>m \<diamond>\<^sup>m\<psi>)"     by auto  
\<comment>\<open>Example 6.10 of Sider (2009) Logic for Philosophy\<close>
  lemma T1a:  "\<Turnstile>\<^sup>m \<box>\<^sup>mp\<^sup>m \<supset>\<^sup>m ((\<diamond>\<^sup>mq\<^sup>m) \<supset>\<^sup>m \<diamond>\<^sup>m (p\<^sup>m \<and>\<^sup>m q\<^sup>m))" by auto  \<comment>\<open>fast automation in meta-logic HOL\<close>
  lemma T1b: "\<Turnstile>\<^sup>m \<box>\<^sup>mp\<^sup>m \<supset>\<^sup>m ((\<diamond>\<^sup>mq\<^sup>m) \<supset>\<^sup>m \<diamond>\<^sup>m (p\<^sup>m \<and>\<^sup>m q\<^sup>m))"                         
    proof -                                                                  \<comment>\<open>alternative interactive proof in modal object logic K\<close>
      have 1: "\<Turnstile>\<^sup>m p\<^sup>m \<supset>\<^sup>m (q\<^sup>m \<supset>\<^sup>m (p\<^sup>m \<and>\<^sup>m q\<^sup>m))"              unfolding AndM_def using H1 H2 H3 MP by metis
      have 2: "\<Turnstile>\<^sup>m \<box>\<^sup>m(p\<^sup>m \<supset>\<^sup>m (q\<^sup>m \<supset>\<^sup>m (p\<^sup>m \<and>\<^sup>m q\<^sup>m)))"                                          using 1 Nec              by metis
      have 3: "\<Turnstile>\<^sup>m \<box>\<^sup>mp\<^sup>m \<supset>\<^sup>m \<box>\<^sup>m(q\<^sup>m \<supset>\<^sup>m (p\<^sup>m \<and>\<^sup>m q\<^sup>m))"                                        using 2 Dist MP        by metis
      have 4: "\<Turnstile>\<^sup>m (\<box>\<^sup>m(q\<^sup>m \<supset>\<^sup>m (p\<^sup>m \<and>\<^sup>m q\<^sup>m))) \<supset>\<^sup>m ((\<diamond>\<^sup>mq\<^sup>m) \<supset>\<^sup>m \<diamond>\<^sup>m(p\<^sup>m \<and>\<^sup>m q\<^sup>m))"  using K_Dia              by metis
      have 5: "\<Turnstile>\<^sup>m \<box>\<^sup>mp\<^sup>m \<supset>\<^sup>m ((\<diamond>\<^sup>mq\<^sup>m) \<supset>\<^sup>m \<diamond>\<^sup>m (p\<^sup>m \<and>\<^sup>m q\<^sup>m))"                               using 3 4 H1 H2 MP by metis 
      thus ?thesis . qed
end