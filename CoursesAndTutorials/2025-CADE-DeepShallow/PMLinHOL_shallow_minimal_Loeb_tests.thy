theory PMLinHOL_shallow_minimal_Loeb_tests imports PMLinHOL_shallow_minimal   (* Christoph Benzmüller, 2025 *)
begin  
\<comment>\<open>Löb axiom: with the minimal shallow embedding automated reasoning tools are still partly responsive\<close>
  lemma Loeb1:   "\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m( \<box>\<^sup>m\<phi> \<supset>\<^sup>m\<phi>) \<supset>\<^sup>m \<box>\<^sup>m\<phi>" nitpick[card \<w>=1,card \<S>=1] oops \<comment>\<open>nitpick: Counterexample.\<close>
  lemma Loeb2:   "(conversewf R \<and> transitive R) \<longrightarrow>  (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m(\<box>\<^sup>m\<phi> \<supset>\<^sup>m\<phi>) \<supset>\<^sup>m \<box>\<^sup>m\<phi>)"  \<comment>\<open>sh: Proof found\<close> oops
  lemma Loeb3:   "(conversewf R \<and> transitive R) \<longleftarrow> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m(\<box>\<^sup>m\<phi> \<supset>\<^sup>m\<phi>) \<supset>\<^sup>m \<box>\<^sup>m\<phi>)"  \<comment>\<open>sh: No Proof\<close> oops
  lemma Loeb3a: "conversewf R \<longleftarrow> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m(\<box>\<^sup>m\<phi> \<supset>\<^sup>m\<phi>) \<supset>\<^sup>m \<box>\<^sup>m\<phi>)" unfolding DefM by blast  
  lemma Loeb3b: "transitive R \<longleftarrow> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m(\<box>\<^sup>m\<phi> \<supset>\<^sup>m\<phi>) \<supset>\<^sup>m \<box>\<^sup>m\<phi>)" \<comment>\<open>sledgehammer: No Proof\<close> oops
  lemma Loeb3c: "irreflexive R \<longleftarrow> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m(\<box>\<^sup>m\<phi> \<supset>\<^sup>m\<phi>) \<supset>\<^sup>m \<box>\<^sup>m\<phi>)"  \<comment>\<open>sledgehammer: Proof found\<close> oops
end


