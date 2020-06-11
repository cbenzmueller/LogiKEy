theory KanckosLethenNo2Actualist imports HOML MFilter BaseDefs
begin  
(*Axioms of Version No. 2 (Kanckos & Lethen, 2019)*)
abbreviation delta ("\<Delta>") where "\<Delta> A \<equiv> \<lambda>x.(\<^bold>\<forall>\<psi>. ((A \<psi>) \<^bold>\<rightarrow> (\<psi> x)))"
abbreviation N ("\<N>") where "\<N> \<phi> \<equiv> \<lambda>x.(\<^bold>\<box> (\<phi> x))"

axiomatization where 
Axiom1: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(((\<P> \<phi>) \<^bold>\<and> (\<phi>\<Rrightarrow>\<psi>)) \<^bold>\<rightarrow> (\<P> \<psi>))\<rfloor>" and
Axiom2: "\<lfloor>\<^bold>\<forall>A .(\<^bold>\<box>((\<^bold>\<forall>\<phi>.((A \<phi>) \<^bold>\<rightarrow>  (\<P> \<phi>))) \<^bold>\<rightarrow> (\<P> (\<Delta> A))))\<rfloor>" and
Axiom3: "\<lfloor>\<^bold>\<forall>\<phi>.((\<P> \<phi>) \<^bold>\<rightarrow> (\<P> (\<N> \<phi>)))\<rfloor>" and
Axiom4: "\<lfloor>\<^bold>\<forall>\<phi>.((\<P> \<phi>) \<^bold>\<rightarrow> (\<^bold>\<not>(\<P>(\<^bold>\<rightharpoondown>\<phi>))))\<rfloor>" and
(*Logic S5*) 
axB:  "\<lfloor>\<^bold>\<forall>\<phi>.(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>)\<rfloor>" and axM: "\<lfloor>\<^bold>\<forall>\<phi>.((\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> \<phi>)\<rfloor>" and ax4:  "\<lfloor>\<^bold>\<forall>\<phi>.((\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<^bold>\<box>\<phi>))\<rfloor>"

(*Sahlqvist correspondences: they are more suited for proof automation*)
lemma axB': "\<forall>x y. \<not>(x\<^bold>ry) \<or> (y\<^bold>rx)" using axB by fastforce
lemma axM': "\<forall>x. (x\<^bold>rx)" using axM by blast
lemma ax4': "\<forall>x y z. (((x\<^bold>ry) \<and> (y\<^bold>rz)) \<longrightarrow> (x\<^bold>rz))" using ax4 by auto

(*Short proof of Theorem T8*)
theorem T8: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y)\<rfloor>" (*Note: fewer assumptions used in some cases than in KanckosLethen 2019*)
proof -
  have T1: "\<lfloor>\<P> \<G>\<rfloor>"  unfolding G_def  using Axiom2 axM by blast
  have T3a: "\<lfloor>\<P> (\<lambda>x. (\<^bold>\<exists>\<^sup>Ey. \<G> y))\<rfloor>" by (metis (no_types, lifting) Axiom1 T1)
  have T3b: "\<lfloor>\<^bold>\<box>(\<P> (\<lambda>x.(\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y))))\<rfloor>" by (smt Axiom1 G_def T3a  Axiom3 T1 axB') 
  have T6: "\<lfloor>\<^bold>\<box>((\<^bold>\<exists>\<^sup>Ey. \<G> y) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y)))\<rfloor>" by (smt G_def T3a T3b) 
  have T7: "\<lfloor>\<^bold>\<box>((\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ey. \<G> y)) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y)))\<rfloor>" using T6 axB' by blast
  thus ?thesis by (smt Axiom1 Axiom4 T3b axB') qed

(*Proofs for all theorems for No.2 from the KanckosLethen paper*)
theorem Theorem0: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.((\<^bold>\<forall>Q. ((Q \<phi>)  \<^bold>\<rightarrow> (Q \<psi>))) \<^bold>\<rightarrow>  ((\<P> \<phi>) \<^bold>\<rightarrow> (\<P>  \<phi>)))\<rfloor>" by auto  (*not needed*)
theorem Theorem1: "\<lfloor>\<P> \<G>\<rfloor>"  unfolding G_def  using Axiom2 axM by blast
theorem Theorem2: "\<lfloor>\<^bold>\<forall>\<^sup>Ex. ((\<G> x)\<^bold>\<rightarrow>(\<^bold>\<exists>\<^sup>Ey. \<G> y))\<rfloor>" by blast  (*not needed*)
theorem Theorem3a: "\<lfloor>\<P> (\<lambda>x. (\<^bold>\<exists>\<^sup>Ey. \<G> y))\<rfloor>"  by (metis (no_types, lifting) Axiom1 Theorem1) 
theorem Theorem3b: "\<lfloor>\<^bold>\<box>(\<P> (\<lambda>x.(\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y))))\<rfloor>" by (smt Axiom1 G_def Theorem3a  Axiom3 Theorem1 axB') 
theorem Theorem4: "\<lfloor>\<^bold>\<forall>\<^sup>Ex. \<^bold>\<box>((\<G> x) \<^bold>\<rightarrow> ((\<P> (\<lambda>x.(\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y)))) \<^bold>\<rightarrow>  (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y))))\<rfloor>" using G_def by fastforce  (*not needed*)
theorem Theorem5: "\<lfloor>\<^bold>\<forall>\<^sup>Ex. \<^bold>\<box>((\<G> x) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y)))\<rfloor>" by (smt G_def Theorem3a Theorem3b)  (*not needed*)
theorem Theorem6: "\<lfloor>\<^bold>\<box>((\<^bold>\<exists>\<^sup>Ey. \<G> y) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y)))\<rfloor>" by (smt G_def Theorem3a Theorem3b) 
theorem Theorem7: "\<lfloor>\<^bold>\<box>((\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ey. \<G> y)) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y)))\<rfloor>" using Theorem6 axB' by blast
theorem Theorem8: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. \<G> y)\<rfloor>" by (metis Axiom1 Axiom4 Theorem1 Theorem7 axB')
theorem Theorem9: "\<lfloor>\<^bold>\<forall>\<phi>. ((\<P> \<phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. \<phi> x))\<rfloor>" using Axiom1 Axiom4 by blast

(*Are the axioms from Benzmüller 2020 implied?*)
(*Actualist version of the axioms as stated Benzmüller 2020*)
 lemma A1': "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" using Theorem9 by blast
 lemma A2': "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> ((X\<^bold>\<sqsubseteq>Y)\<^bold>\<or>(X\<Rrightarrow>Y))) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" sledgehammer nitpick oops (*no answer, yet*)
 lemma A3:  "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>" sledgehammer nitpick oops (*no answer, yet*)
(*Possibilist version of the axioms*)
 lemma A1'P: "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" using Theorem9 by blast
 lemma A2'P: "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> ((\<^bold>\<forall>z. ((X z) \<^bold>\<rightarrow> (Y z)))\<^bold>\<or>(\<^bold>\<box>(\<^bold>\<forall>z. ((X z) \<^bold>\<rightarrow> (Y z)))))) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" 
   sledgehammer nitpick oops (*no answer, yet*)
 lemma A2'aP: "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (\<^bold>\<box>(\<^bold>\<forall>z. ((X z) \<^bold>\<rightarrow> (Y z))))) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" using Axiom1 by blast 
 lemma A2'bP: "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (\<^bold>\<forall>z. ((X z) \<^bold>\<rightarrow> (Y z)))) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" 
   sledgehammer nitpick[timeout=300] oops (*no answer, yet*)
 lemma A3P:  "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((\<^bold>\<box>(\<^bold>\<forall>u.((X u) \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y.((\<Z> Y) \<^bold>\<rightarrow> (Y u)))))) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>"  
   sledgehammer nitpick oops (*no answer, yet*)
end

