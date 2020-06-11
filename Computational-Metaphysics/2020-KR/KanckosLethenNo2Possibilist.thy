theory KanckosLethenNo2Possibilist imports HOML MFilter BaseDefs
begin  
(*Axioms of Version No. 2 (Kanckos & Lethen, 2019)*)
abbreviation delta ("\<Delta>") where "\<Delta> A \<equiv> \<lambda>x.(\<^bold>\<forall>\<psi>. ((A \<psi>) \<^bold>\<rightarrow> (\<psi> x)))"
abbreviation N ("\<N>") where "\<N> \<phi> \<equiv> \<lambda>x.(\<^bold>\<box> (\<phi> x))"

axiomatization where 
Axiom1: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(((\<P> \<phi>) \<^bold>\<and> (\<^bold>\<box>(\<^bold>\<forall>x. ((\<phi> x) \<^bold>\<rightarrow> (\<psi> x))))) \<^bold>\<rightarrow> (\<P> \<psi>))\<rfloor>" and
Axiom2: "\<lfloor>\<^bold>\<forall>A .(\<^bold>\<box>((\<^bold>\<forall>\<phi>.((A \<phi>) \<^bold>\<rightarrow>  (\<P> \<phi>))) \<^bold>\<rightarrow> (\<P> (\<Delta> A))))\<rfloor>" and
Axiom3: "\<lfloor>\<^bold>\<forall>\<phi>.((\<P> \<phi>) \<^bold>\<rightarrow> (\<P> (\<N> \<phi>)))\<rfloor>" and
Axiom4: "\<lfloor>\<^bold>\<forall>\<phi>.((\<P> \<phi>) \<^bold>\<rightarrow> (\<^bold>\<not>(\<P>(\<^bold>\<rightharpoondown>\<phi>))))\<rfloor>" and
(*Logic S5*) 
axB:  "\<lfloor>\<^bold>\<forall>\<phi>.(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>)\<rfloor>" and axM: "\<lfloor>\<^bold>\<forall>\<phi>.((\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> \<phi>)\<rfloor>" and ax4:  "\<lfloor>\<^bold>\<forall>\<phi>.((\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<^bold>\<box>\<phi>))\<rfloor>"

(*Sahlqvist correspondences: they are more suited for proof automation*)
lemma axB': "\<forall>x y. \<not>(x\<^bold>ry) \<or> (y\<^bold>rx)" using axB by fastforce
lemma axM': "\<forall>x. (x\<^bold>rx)" using axM by blast
lemma ax4': "\<forall>x y z. (((x\<^bold>ry) \<and> (y\<^bold>rz)) \<longrightarrow> (x\<^bold>rz))" using ax4 by auto 

(*Proofs for all theorems for No.2 from the Kanckos&Lethen paper*)
theorem Theorem0: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.((\<^bold>\<forall>Q. ((Q \<phi>)  \<^bold>\<rightarrow> (Q \<psi>))) \<^bold>\<rightarrow>  ((\<P> \<phi>) \<^bold>\<rightarrow> (\<P>  \<phi>)))\<rfloor>" by auto  (*not needed*)
theorem Theorem1: "\<lfloor>\<P> \<G>\<rfloor>"  unfolding G_def  using Axiom2 axM by blast
theorem Theorem2: "\<lfloor>\<^bold>\<forall>x. ((\<G> x)\<^bold>\<rightarrow>(\<^bold>\<exists>y. \<G> y))\<rfloor>" by blast  (*not needed*)
theorem Theorem3a: "\<lfloor>\<P> (\<lambda>x. (\<^bold>\<exists>y. \<G> y))\<rfloor>"  by (metis (no_types, lifting) Axiom1 Theorem1) 
theorem Theorem3b: "\<lfloor>\<^bold>\<box>(\<P> (\<lambda>x.(\<^bold>\<box>(\<^bold>\<exists>y. \<G> y))))\<rfloor>" by (smt Axiom1 G_def Theorem3a  Axiom3 Theorem1 axB') 
theorem Theorem4: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<box>((\<G> x) \<^bold>\<rightarrow> ((\<P> (\<lambda>x.(\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)))) \<^bold>\<rightarrow>  (\<^bold>\<box>(\<^bold>\<exists>y. \<G> y))))\<rfloor>" using G_def by fastforce (*not needed*)
theorem Theorem5: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<box>((\<G> x) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)))\<rfloor>" by (smt G_def Theorem3a Theorem3b)  (*not needed*)
theorem Theorem6: "\<lfloor>\<^bold>\<box>((\<^bold>\<exists>y. \<G> y) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)))\<rfloor>" by (smt G_def Theorem3a Theorem3b) 
theorem Theorem7: "\<lfloor>\<^bold>\<box>((\<^bold>\<diamond>(\<^bold>\<exists>y. \<G> y)) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)))\<rfloor>" using Theorem6 axB' by blast
theorem Theorem8: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)\<rfloor>" by (metis Axiom1 Axiom4 Theorem1 Theorem7 axB')
theorem Theorem9: "\<lfloor>\<^bold>\<forall>\<phi>. ((\<P> \<phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>x. \<phi> x))\<rfloor>" using Axiom1 Axiom4 by blast

(*Short proof of Theorem8; analogous to the one presented in Sec. 7 of Benzmüller 2020*)
theorem "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)\<rfloor>" (* Note: this version of the proof uses only axB' and axM' *)
 proof -
   have L1: "\<lfloor>(\<^bold>\<exists>X.((\<P> X)\<^bold>\<and>\<^bold>\<not>(\<^bold>\<exists>X)))\<^bold>\<rightarrow>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>"  using Axiom1 Axiom3 axB' by blast  
   have L2:  "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" using Axiom1 Axiom4 by blast 
   have L3: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>X.((\<P> X) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists> X)))\<rfloor>" using L1 L2 by blast 
   have T2: "\<lfloor>\<P> \<G>\<rfloor>" by (smt Axiom1 Axiom2 G_def axM')
   have T3: "\<lfloor>\<^bold>\<exists>y. \<G> y\<rfloor>" using L3 T2 by blast
   have T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)\<rfloor>" by (simp add: T3)
  thus ?thesis by blast qed

theorem T5: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>y. \<G> y)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>y. \<G> y)\<rfloor>" (* Obvious: If we can prove Theorem8, then we also have T5 *)
 proof -
   have L1: "\<lfloor>(\<^bold>\<exists>X.((\<P> X)\<^bold>\<and>\<^bold>\<not>(\<^bold>\<exists>X)))\<^bold>\<rightarrow>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>"  using Axiom1 Axiom3 axB' by blast  
   have L2:  "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" using Axiom1 Axiom4 by blast 
   have L3: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>X.((\<P> X) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists> X)))\<rfloor>" using L1 L2 by blast 
   have T2: "\<lfloor>\<P> \<G>\<rfloor>" by (smt Axiom1 Axiom2 G_def axM')
   have T3: "\<lfloor>\<^bold>\<exists>y. \<G> y\<rfloor>" using L3 T2 by blast
   have T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)\<rfloor>" by (simp add: T3)
  thus ?thesis by blast qed

(*Another short proof of Theorem8*)
theorem "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)\<rfloor>"  (*Note: fewer assumptions used in some cases than in Kanckos&Lethen 2019*)
proof -
  have T1: "\<lfloor>\<P> \<G>\<rfloor>"  unfolding G_def  using Axiom2 axM by blast
  have T3a: "\<lfloor>\<P> (\<lambda>x. (\<^bold>\<exists>y. \<G> y))\<rfloor>" by (metis (no_types, lifting) Axiom1 T1)
  have T3b: "\<lfloor>\<^bold>\<box>(\<P> (\<lambda>x.(\<^bold>\<box>(\<^bold>\<exists>y. \<G> y))))\<rfloor>" by (smt Axiom1 G_def T3a  Axiom3 T1 axB') 
  have T6: "\<lfloor>\<^bold>\<box>((\<^bold>\<exists>y. \<G> y) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)))\<rfloor>" by (smt G_def T3a T3b) 
  have T7: "\<lfloor>\<^bold>\<box>((\<^bold>\<diamond>(\<^bold>\<exists>y. \<G> y)) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>y. \<G> y)))\<rfloor>" using T6 axB' by blast
  thus ?thesis  by (smt Axiom1 Axiom4 T3b axB') qed

(*Are the axioms of the simplified versions of  Benzmüller 2020 implied?*)
(*Actualist version of the axioms*)
 lemma A1': "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" using Theorem9 by blast
 lemma A2': "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> ((X\<^bold>\<sqsubseteq>Y)\<^bold>\<or>(X\<Rrightarrow>Y))) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" nitpick oops (*countermodel*)
 lemma A3:  "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>" nitpick oops (*countermodel*)

(*Possibilist version of the axioms*)
 abbreviation a ("_\<^bold>\<sqsubseteq>\<^sup>p_") where "X\<^bold>\<sqsubseteq>\<^sup>pY \<equiv> \<^bold>\<forall>z.((X z) \<^bold>\<rightarrow> (Y z))"
 abbreviation b ("_\<Rrightarrow>\<^sup>p_") where "X\<Rrightarrow>\<^sup>pY \<equiv> \<^bold>\<box>(X\<^bold>\<sqsubseteq>\<^sup>pY)"
 abbreviation d ("_\<Sqinter>\<^sup>p_") where "X\<Sqinter>\<^sup>p\<Z> \<equiv> \<^bold>\<box>(\<^bold>\<forall>u.((X u) \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y.((\<Z> Y) \<^bold>\<rightarrow> (Y u)))))"

 lemma A1'P: "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" using Theorem9 by blast
 lemma A2'P: "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> ((X\<^bold>\<sqsubseteq>\<^sup>pY)\<^bold>\<or>(X\<Rrightarrow>\<^sup>pY))) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>"  sledgehammer nitpick oops (*no answer, yet*)
 lemma A2'aP: "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (X\<Rrightarrow>\<^sup>pY)) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" using Axiom1 by blast 
 lemma A2'bP: "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (X\<^bold>\<sqsubseteq>\<^sup>pY)) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" sledgehammer nitpick oops (*no answer, yet*)
 lemma A3P:  "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<^sup>p\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>" sledgehammer (Axiom1 Axiom2 axM') oops (*proof found*)

 (*Are Axiom2 and A3 equivalent? Only when assuming Axiom1 and axiom M*)
 lemma  "\<lfloor>\<^bold>\<forall>A .(\<^bold>\<box>((\<^bold>\<forall>\<phi>.((A \<phi>) \<^bold>\<rightarrow>  (\<P> \<phi>))) \<^bold>\<rightarrow> (\<P> (\<Delta> A))))\<rfloor> \<equiv> \<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<^sup>p\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>"
  sledgehammer (Axiom1 axM') oops (*proof found*)
end

(*
(*Are Axiom2 and A3 equivalent? Only when assuming Axiom1 and axiom M*)
 lemma  "\<lfloor>\<^bold>\<forall>A .(\<^bold>\<box>((\<^bold>\<forall>\<phi>.((A \<phi>) \<^bold>\<rightarrow>  (\<P> \<phi>))) \<^bold>\<rightarrow> (\<P> (\<Delta> A))))\<rfloor> \<equiv> \<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<^sup>p\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>"
  sledgehammer (Axiom1 axM') oops (*proof found*)

lemma assumes  A3'P': "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<^sup>p\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>" 
  shows Axiom2': "\<lfloor>\<^bold>\<forall>A .(\<^bold>\<box>((\<^bold>\<forall>\<phi>.((A \<phi>) \<^bold>\<rightarrow>  (\<P> \<phi>))) \<^bold>\<rightarrow> (\<P> (\<Delta> A))))\<rfloor>" 
  using assms by auto

lemma assumes Axiom2': "\<lfloor>\<^bold>\<forall>A .(\<^bold>\<box>((\<^bold>\<forall>\<phi>.((A \<phi>) \<^bold>\<rightarrow>  (\<P> \<phi>))) \<^bold>\<rightarrow> (\<P> (\<Delta> A))))\<rfloor>" 
  shows A3'P': "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<^sup>p\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>" 
  sledgehammer (assms) nitpick oops 

lemma assumes Axiom2': "\<lfloor>\<^bold>\<forall>A .(\<^bold>\<box>((\<^bold>\<forall>\<phi>.((A \<phi>) \<^bold>\<rightarrow>  (\<P> \<phi>))) \<^bold>\<rightarrow> (\<P> (\<Delta> A))))\<rfloor>" 
                     and Axiom1': "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(((\<P> \<phi>) \<^bold>\<and> (\<^bold>\<box>(\<^bold>\<forall>x. ((\<phi> x) \<^bold>\<rightarrow> (\<psi> x))))) \<^bold>\<rightarrow> (\<P> \<psi>))\<rfloor>"
  shows A3'P': "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<^sup>p\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>" 
  sledgehammer (assms axM') nitpick oops 
*)








