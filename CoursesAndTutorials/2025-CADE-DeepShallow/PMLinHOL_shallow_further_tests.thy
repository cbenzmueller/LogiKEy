theory PMLinHOL_shallow_further_tests imports PMLinHOL_shallow_tests                    (* Christoph Benzmüller, 2025 *)
begin             
\<comment>\<open>Implied modal principle\<close>
  lemma K_Dia: "\<Turnstile>\<^sup>s (\<box>\<^sup>s(\<phi> \<supset>\<^sup>s \<psi>)) \<supset>\<^sup>s ((\<diamond>\<^sup>s\<phi>) \<supset>\<^sup>s \<diamond>\<^sup>s\<psi>)"  by auto  
\<comment>\<open>Example 6.10 of Sider (2009) Logic for Philosophy\<close> 
  lemma T1a:  "\<Turnstile>\<^sup>s \<box>\<^sup>sp\<^sup>s \<supset>\<^sup>s ((\<diamond>\<^sup>sq\<^sup>s) \<supset>\<^sup>s \<diamond>\<^sup>s (p\<^sup>s \<and>\<^sup>s q\<^sup>s))"  by auto  \<comment>\<open>fast automation in meta-logic HOL\<close>
  lemma T1b: "\<Turnstile>\<^sup>s \<box>\<^sup>sp\<^sup>s \<supset>\<^sup>s ((\<diamond>\<^sup>sq\<^sup>s) \<supset>\<^sup>s \<diamond>\<^sup>s (p\<^sup>s \<and>\<^sup>s q\<^sup>s))"                         
    proof -                                                                       \<comment>\<open>alternative interactive proof in modal object logic K\<close>
      have 1: "\<Turnstile>\<^sup>s p\<^sup>s \<supset>\<^sup>s (q\<^sup>s \<supset>\<^sup>s (p\<^sup>s \<and>\<^sup>s q\<^sup>s))"              unfolding AndS_def using H1 H2 H3 MP  by metis
      have 2: "\<Turnstile>\<^sup>s \<box>\<^sup>s(p\<^sup>s \<supset>\<^sup>s (q\<^sup>s \<supset>\<^sup>s (p\<^sup>s \<and>\<^sup>s q\<^sup>s)))"                                           using 1 Nec              by metis
      have 3: "\<Turnstile>\<^sup>s \<box>\<^sup>sp\<^sup>s \<supset>\<^sup>s \<box>\<^sup>s(q\<^sup>s \<supset>\<^sup>s (p\<^sup>s \<and>\<^sup>s q\<^sup>s))"                                         using 2 Dist MP        by metis
      have 4: "\<Turnstile>\<^sup>s (\<box>\<^sup>s(q\<^sup>s \<supset>\<^sup>s (p\<^sup>s \<and>\<^sup>s q\<^sup>s))) \<supset>\<^sup>s ((\<diamond>\<^sup>sq\<^sup>s) \<supset>\<^sup>s \<diamond>\<^sup>s(p\<^sup>s \<and>\<^sup>s q\<^sup>s))"        using K_Dia              by metis
      have 5: "\<Turnstile>\<^sup>s \<box>\<^sup>sp\<^sup>s \<supset>\<^sup>s ((\<diamond>\<^sup>sq\<^sup>s) \<supset>\<^sup>s \<diamond>\<^sup>s (p\<^sup>s \<and>\<^sup>s q\<^sup>s))"                                 using 3 4 H1 H2 MP  by metis 
      thus ?thesis . qed
end