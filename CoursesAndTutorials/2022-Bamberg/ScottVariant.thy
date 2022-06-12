theory ScottVariant imports HOML          (*C. Benzmüller, 2021*)
begin  
(*Positive properties*) 
consts posProp::"\<gamma>\<Rightarrow>\<sigma>" ("\<P>")

(*Definition of God-like*)
definition G ("\<G>") where "\<G>(x) \<equiv> \<^bold>\<forall>\<Phi>.(\<P>(\<Phi>) \<^bold>\<rightarrow> \<Phi>(x))"

(*Definitions of Essence and Necessary Existence*)
definition Ess ("_Ess._"[80,80]81) 
  where "\<Phi> Ess. x \<equiv> \<Phi>(x) \<^bold>\<and> (\<^bold>\<forall>\<Psi>. \<Psi>(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi>(y) \<^bold>\<rightarrow> \<Psi>(y)))"
definition NE ("\<N>\<E>") where "\<N>\<E>(x) \<equiv> \<^bold>\<forall>\<Phi>. \<Phi> Ess. x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>x. (\<Phi>(x)))"

(*Axioms of Scott's variant*)
axiomatization where 
 AXIOM1: "\<lfloor>\<^bold>\<forall>\<Phi>. \<P>(\<^bold>\<not>\<Phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>\<P>(\<Phi>)\<rfloor>" and
 AXIOM2: "\<lfloor>\<^bold>\<forall>\<Phi> \<Psi>. \<P>(\<Phi>) \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> \<P>(\<Psi>)\<rfloor>" and
 AXIOM3: "\<lfloor>\<P>(\<G>)\<rfloor>" and
 AXIOM4: "\<lfloor>\<^bold>\<forall>\<Phi>. \<P>(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<P>(\<Phi>)\<rfloor>" and
 AXIOM5: "\<lfloor>\<P>(\<N>\<E>)\<rfloor>" 

(*We only need the B axiom*)
axiomatization where B:  "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<Phi>\<rfloor>" (*Logic KB*)
lemma B': "\<forall>x y. \<not>x\<^bold>ry \<or> y\<^bold>rx" using B by fastforce

(*Verifying Scott's proof from*)
theorem THEOREM1: "\<lfloor>\<^bold>\<forall>\<Phi>. \<P>(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>x. \<Phi>(x))\<rfloor>" 
  using AXIOM1 AXIOM2 by blast
theorem CORO: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" using THEOREM1 AXIOM3 by simp
theorem THEOREM2: "\<lfloor>\<^bold>\<forall>x. \<G>(x)\<^bold>\<rightarrow> \<G> Ess. x\<rfloor>" 
  by (smt AXIOM1 AXIOM4 Ess_def G_def)
theorem THEOREM3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" 
  by (metis AXIOM5 B' CORO G_def NE_def THEOREM2)

theorem THEOREM4: "\<lfloor>\<^bold>\<exists>x. \<G>(x)\<rfloor>" using B' CORO THEOREM3 by blast

lemma C1: "\<lfloor>\<^bold>\<not>\<P>(\<lambda>x. x\<^bold>\<noteq>x)\<rfloor>" using AXIOM1 AXIOM2 by blast
lemma C1': "\<lfloor>\<^bold>\<not>\<P>(\<lambda>x. \<^bold>\<bottom>)\<rfloor>" using AXIOM1 AXIOM2 by blast
lemma C2: "\<lfloor>\<^bold>\<forall>\<Phi> \<Psi>. \<P>(\<Phi>) \<^bold>\<and> (\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> \<P>(\<Psi>)\<rfloor>" 
   by (metis AXIOM1 G_def THEOREM4)

(*Consistency*) 
lemma True nitpick[satisfy] oops (*Model found*)
end





(*
(*Further Corollaries of Scott's theory*)
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>\<rfloor>" (*Modal collapse: holds*)
proof - {fix w fix Q
 have 1: "\<forall>x. \<G>(x)(w) \<longrightarrow> (\<^bold>\<forall>Z. Z(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>z. \<G>(z) \<^bold>\<rightarrow> Z(z)))(w)" 
         by (metis AXIOM1 AXIOM4 G_def)
 have 2: "(\<exists>x. \<G>(x)(w)) \<longrightarrow> (Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>z. (\<G> z) \<^bold>\<rightarrow> Q))(w)" 
         using 1 by force
 have 3: "(Q \<^bold>\<rightarrow> \<^bold>\<box>Q)(w)" using B' THEOREM3 2 by blast} 
 thus ?thesis by auto qed

*)


(*
(*The simplified version in appendix C is implied*) 
lemma  A1':  "\<lfloor>\<P>(\<lambda>x. x\<^bold>=x) \<^bold>\<and> \<^bold>\<not>\<P>(\<lambda>x. x\<^bold>\<noteq>x)\<rfloor>" using A1 A2 by blast
lemma A2'': "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X\<^bold>\<sqsubseteq>Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" by (metis A1 A2 B G_def T6)
lemma T2:   "\<lfloor>\<P> \<G>\<rfloor>" by (metis A3 G_def)
*)

(*
theorem T6again: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> \<G>)\<rfloor>"  
proof -
 have L1: "\<lfloor>(\<^bold>\<exists>X. \<P> X \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists> X)) \<^bold>\<rightarrow> \<P>(\<lambda>x. x\<^bold>\<noteq>x)\<rfloor>" 
   by (metis A2 B G_def T6)
 have L2: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>X. \<P> X \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists> X))\<rfloor>" 
   using A1 A2 L1 by blast 
 have T1': "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> (\<^bold>\<exists> X)\<rfloor>" by (metis L2)  
 have T3': "\<lfloor>\<^bold>\<exists> \<G>\<rfloor>"
   by (metis A2 A5 B L2 T6)
 have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists> \<G>)\<rfloor>" 
   using A1 A2 T3' by blast (*not needed*)
 have T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> \<G>)\<rfloor>" by (metis T3') 
 thus ?thesis by simp qed
*)