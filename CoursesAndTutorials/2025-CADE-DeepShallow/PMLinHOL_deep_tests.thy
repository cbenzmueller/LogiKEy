theory PMLinHOL_deep_tests imports PMLinHOL_deep                                                 (* Christoph Benzmüller, 2025 *)
begin                 
\<comment>\<open>Hilbert calculus: proving that the schematic axioms and rules are implied by the embedding\<close>
  lemma H1: "\<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d (\<psi> \<supset>\<^sup>d \<phi>)" by auto
  lemma H2: "\<Turnstile>\<^sup>d (\<phi> \<supset>\<^sup>d (\<psi> \<supset>\<^sup>d \<gamma>)) \<supset>\<^sup>d ((\<phi> \<supset>\<^sup>d \<psi>) \<supset>\<^sup>d (\<phi> \<supset>\<^sup>d \<gamma>)) " by auto
  lemma H3: "\<Turnstile>\<^sup>d (\<not>\<^sup>d\<phi> \<supset>\<^sup>d \<not>\<^sup>d\<psi>) \<supset>\<^sup>d (\<psi> \<supset>\<^sup>d \<phi>)" by auto
  lemma MP: "\<Turnstile>\<^sup>d \<phi> \<Longrightarrow> \<Turnstile>\<^sup>d (\<phi>  \<supset>\<^sup>d \<psi>) \<Longrightarrow> \<Turnstile>\<^sup>d \<psi>" by auto
\<comment>\<open>Reasoning with the Hilbert calculus: interactive and fully automated\<close>
  lemma HCderived1: "\<Turnstile>\<^sup>d (\<phi> \<supset>\<^sup>d \<phi>)" \<comment>\<open>sledgehammer(H1 H2 H3 MP) returns: by (metis H1 H2 MP)\<close>  
    proof - have 1: "\<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d ((\<psi> \<supset>\<^sup>d \<phi>) \<supset>\<^sup>d \<phi>)" using H1 by auto 
                 have 2: "\<Turnstile>\<^sup>d (\<phi> \<supset>\<^sup>d ((\<psi> \<supset>\<^sup>d \<phi>) \<supset>\<^sup>d \<phi>)) \<supset>\<^sup>d ((\<phi> \<supset>\<^sup>d (\<psi> \<supset>\<^sup>d \<phi>)) \<supset>\<^sup>d (\<phi> \<supset>\<^sup>d \<phi>))" using H2 by auto 
                 have 3: "\<Turnstile>\<^sup>d (\<phi> \<supset>\<^sup>d (\<psi> \<supset>\<^sup>d \<phi>)) \<supset>\<^sup>d (\<phi> \<supset>\<^sup>d \<phi>)" using 1 2 MP by meson
                 have 4: "\<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d (\<psi>  \<supset>\<^sup>d \<phi>)" using H1 by auto   
                 thus ?thesis using 3 4 MP by meson qed
  lemma HCderived2: "\<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d (\<not>\<^sup>d\<phi>  \<supset>\<^sup>d \<psi>) " by (metis H1 H2 H3 MP) 
  lemma HCderived3: "\<Turnstile>\<^sup>d (\<not>\<^sup>d\<phi>  \<supset>\<^sup>d \<phi>) \<supset>\<^sup>d \<phi>" by (metis H1 H2 H3 MP) 
  lemma HCderived4: "\<Turnstile>\<^sup>d (\<phi> \<supset>\<^sup>d \<psi>) \<supset>\<^sup>d (\<not>\<^sup>d\<psi> \<supset>\<^sup>d \<not>\<^sup>d\<phi>) " by auto   
\<comment>\<open>Modal logic: the schematic necessitation rule and distribution axiom are implied\<close>
  lemma Nec: "\<Turnstile>\<^sup>d \<phi> \<Longrightarrow> \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi>" by auto
  lemma Dist: "\<Turnstile>\<^sup>d \<box>\<^sup>d(\<phi> \<supset>\<^sup>d \<psi>) \<supset>\<^sup>d (\<box>\<^sup>d\<phi> \<supset>\<^sup>d \<box>\<^sup>d\<psi>) " by auto
\<comment>\<open>Correspondence theory: correct statements\<close> 
(**)  lemma cM:  "reflexive R \<longleftrightarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi> \<supset>\<^sup>d \<phi>)" \<comment>\<open>sledgehammer: No proof found\<close> oops 
  lemma cBa: "symmetric R \<longrightarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>))" by auto 
(**)  lemma cBb: "symmetric R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>))" \<comment>\<open>sledgehammer: No proof\<close> oops
  lemma c4a: "transitive R \<longrightarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>))" using RelativeTruthD.simps by metis
(**)  lemma c4b: "transitive R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>))" \<comment>\<open>sledgehammer: No proof\<close> oops
\<comment>\<open>Correspondence theory: incorrect statements\<close> 
  lemma "reflexive R \<longrightarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>))" nitpick[card \<w>=3] oops \<comment>\<open>nitpick: Cex.\<close>
\<comment>\<open>Simple, incorrect validity statements\<close>
  lemma "\<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d\<phi>" nitpick[card \<w>=2, card \<S>=1] oops \<comment>\<open>nitpick: Counterexample: modal collapse not implied\<close>
  lemma "\<Turnstile>\<^sup>d \<box>\<^sup>d( \<box>\<^sup>d\<phi> \<supset>\<^sup>d  \<box>\<^sup>d\<psi>) \<or>\<^sup>d \<box>\<^sup>d( \<box>\<^sup>d\<psi> \<supset>\<^sup>d  \<box>\<^sup>d\<phi>)" nitpick[card \<w>=3] oops \<comment>\<open>nitpick: Counterexample\<close>
  lemma "\<Turnstile>\<^sup>d (\<diamond>\<^sup>d(\<box>\<^sup>d \<phi>)) \<supset>\<^sup>d  \<box>\<^sup>d(\<diamond>\<^sup>d \<phi>)" nitpick[card \<w>=2] oops \<comment>\<open>nitpick: Counterexample\<close> 
\<comment>\<open>Implied axiom schemata in S5\<close>
  lemma KB: "symmetric R \<longrightarrow> (\<forall>\<phi> \<psi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<diamond>\<^sup>d(\<box>\<^sup>d\<phi>)) \<supset>\<^sup>d  \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>))" by auto
  lemma K4B: "symmetric R \<and> transitive R 
       \<longrightarrow> (\<forall>\<phi> \<psi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<box>\<^sup>d( \<box>\<^sup>d\<phi> \<supset>\<^sup>d  \<box>\<^sup>d\<psi>) \<or>\<^sup>d \<box>\<^sup>d( \<box>\<^sup>d\<psi> \<supset>\<^sup>d  \<box>\<^sup>d\<phi>))" by (smt OrD_def RelativeTruthD.simps)
end


