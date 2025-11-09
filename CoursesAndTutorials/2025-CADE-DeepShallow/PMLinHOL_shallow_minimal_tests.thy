theory PMLinHOL_shallow_minimal_tests imports PMLinHOL_shallow_minimal            (* Christoph Benzmüller, 2025 *)
begin                 
\<comment>\<open>Hilbert calculus: proving that the schematic axioms and rules are implied by the embedding\<close>
  lemma H1: "\<Turnstile>\<^sup>m \<phi> \<supset>\<^sup>m (\<psi> \<supset>\<^sup>m \<phi>)" by auto
  lemma H2: "\<Turnstile>\<^sup>m (\<phi> \<supset>\<^sup>m (\<psi> \<supset>\<^sup>m \<gamma>)) \<supset>\<^sup>m ((\<phi> \<supset>\<^sup>m \<psi>) \<supset>\<^sup>m (\<phi> \<supset>\<^sup>m \<gamma>)) " by auto
  lemma H3: "\<Turnstile>\<^sup>m (\<not>\<^sup>m\<phi>  \<supset>\<^sup>m \<not>\<^sup>m\<psi>) \<supset>\<^sup>m (\<psi> \<supset>\<^sup>m \<phi>)" by auto
  lemma MP: "\<Turnstile>\<^sup>m \<phi> \<Longrightarrow> \<Turnstile>\<^sup>m (\<phi>  \<supset>\<^sup>m \<psi>) \<Longrightarrow> \<Turnstile>\<^sup>m \<psi>" by auto
\<comment>\<open>Reasoning with the Hilbert calculus: interactive and fully automated\<close>
  lemma HCderived1: "\<Turnstile>\<^sup>m (\<phi> \<supset>\<^sup>m \<phi>)" \<comment>\<open>sledgehammer(H1 H2 H3 MP) returns: by (metis H1 H2 MP)\<close>  
    proof -  have 1: "\<Turnstile>\<^sup>m \<phi> \<supset>\<^sup>m ((\<psi> \<supset>\<^sup>m \<phi>) \<supset>\<^sup>m \<phi>)" using H1 by auto 
                 have 2: "\<Turnstile>\<^sup>m (\<phi> \<supset>\<^sup>m ((\<psi> \<supset>\<^sup>m \<phi>) \<supset>\<^sup>m \<phi>)) \<supset>\<^sup>m ((\<phi> \<supset>\<^sup>m (\<psi> \<supset>\<^sup>m \<phi>)) \<supset>\<^sup>m (\<phi> \<supset>\<^sup>m \<phi>))" using H2 by auto 
                 have 3: "\<Turnstile>\<^sup>m (\<phi> \<supset>\<^sup>m (\<psi> \<supset>\<^sup>m \<phi>)) \<supset>\<^sup>m (\<phi> \<supset>\<^sup>m \<phi>)" using 1 2 MP by meson
                 have 4: "\<Turnstile>\<^sup>m \<phi> \<supset>\<^sup>m (\<psi>  \<supset>\<^sup>m \<phi>)" using H1 by auto   
                 thus ?thesis using 3 4 MP by meson qed
  lemma HCderived2: "\<Turnstile>\<^sup>m \<phi> \<supset>\<^sup>m (\<not>\<^sup>m\<phi>  \<supset>\<^sup>m \<psi>) " by (metis H1 H2 H3 MP) 
  lemma HCderived3: "\<Turnstile>\<^sup>m (\<not>\<^sup>m\<phi>  \<supset>\<^sup>m \<phi>) \<supset>\<^sup>m \<phi>" by (metis H1 H2 H3 MP) 
  lemma HCderived4: "\<Turnstile>\<^sup>m (\<phi> \<supset>\<^sup>m \<psi>) \<supset>\<^sup>m (\<not>\<^sup>m\<psi> \<supset>\<^sup>m \<not>\<^sup>m\<phi>) " by auto
\<comment>\<open>Modal logic: the schematic necessitation rule and distribution axiom are implied\<close>
  lemma Nec: "\<Turnstile>\<^sup>m \<phi> \<Longrightarrow> \<Turnstile>\<^sup>m \<box>\<^sup>m\<phi>" by (smt DefM)
  lemma Dist:  "\<Turnstile>\<^sup>m \<box>\<^sup>m(\<phi> \<supset>\<^sup>m \<psi>) \<supset>\<^sup>m (\<box>\<^sup>m\<phi> \<supset>\<^sup>m \<box>\<^sup>m\<psi>) " by auto
\<comment>\<open>Correspondence theory: correct statements\<close> 
  lemma cM:  "reflexive R \<longleftrightarrow> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m\<phi> \<supset>\<^sup>m \<phi>)" by auto
  lemma cBa: "symmetric R \<longrightarrow> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<phi> \<supset>\<^sup>m \<box>\<^sup>m\<diamond>\<^sup>m\<phi>)" by auto 
  lemma cBb: "symmetric R \<longleftarrow> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<phi> \<supset>\<^sup>m \<box>\<^sup>m\<diamond>\<^sup>m\<phi>)" by (metis DefM)
  lemma c4a: "transitive R \<longrightarrow> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m\<phi> \<supset>\<^sup>m \<box>\<^sup>m(\<box>\<^sup>m\<phi>))" by (smt DefM)
  lemma c4b: "transitive R \<longleftarrow> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m\<phi> \<supset>\<^sup>m \<box>\<^sup>m(\<box>\<^sup>m\<phi>))" by auto
\<comment>\<open>Correspondence theory: incorrect statements\<close> 
  lemma "reflexive R \<longrightarrow> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m\<phi> \<supset>\<^sup>m \<box>\<^sup>m(\<box>\<^sup>m\<phi>))" nitpick[card \<w>=3,show_all] oops \<comment>\<open>nitpick: Counterexample\<close>
\<comment>\<open>Simple, incorrect validity statements\<close>
  lemma "\<Turnstile>\<^sup>m \<phi> \<supset>\<^sup>m \<box>\<^sup>m\<phi>" nitpick[card \<w>=2, card \<S>= 1] oops \<comment>\<open>nitpick: Counterexample: modal collapse not implied\<close>
  lemma "\<Turnstile>\<^sup>m \<box>\<^sup>m( \<box>\<^sup>m\<phi> \<supset>\<^sup>m  \<box>\<^sup>m\<psi>) \<or>\<^sup>m \<box>\<^sup>m( \<box>\<^sup>m\<psi> \<supset>\<^sup>m  \<box>\<^sup>m\<phi>)" nitpick[card \<w>=3] oops \<comment>\<open>nitpick: Counterexample\<close> 
  lemma "\<Turnstile>\<^sup>m (\<diamond>\<^sup>m(\<box>\<^sup>m \<phi>)) \<supset>\<^sup>m  \<box>\<^sup>m(\<diamond>\<^sup>m \<phi>)" nitpick[card \<w>=2] oops \<comment>\<open>nitpick: Counterexample\<close> 
\<comment>\<open>Implied axiom schemata in S5\<close>
  lemma KB: "symmetric R \<longrightarrow> (\<forall>\<phi> \<psi>.  \<Turnstile>\<^sup>m (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)) \<supset>\<^sup>m  \<box>\<^sup>m(\<diamond>\<^sup>m\<phi>))" by auto
  lemma K4B: "symmetric R \<and> transitive R \<longrightarrow> (\<forall>\<phi> \<psi>. \<Turnstile>\<^sup>m \<box>\<^sup>m( \<box>\<^sup>m\<phi> \<supset>\<^sup>m  \<box>\<^sup>m\<psi>) \<or>\<^sup>m \<box>\<^sup>m( \<box>\<^sup>m\<psi> \<supset>\<^sup>m  \<box>\<^sup>m\<phi>))" by (smt DefM)
end


