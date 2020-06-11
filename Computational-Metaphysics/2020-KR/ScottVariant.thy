theory ScottVariant imports HOML MFilter BaseDefs
begin  
(*Axioms of Scott's variant*)
axiomatization where 
 A1: "\<lfloor>\<^bold>\<forall>X.((\<^bold>\<not>(\<P> X)) \<^bold>\<leftrightarrow> (\<P>(\<^bold>\<rightharpoondown>X)))\<rfloor>" and
 A2: "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (X\<Rrightarrow>Y)) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" and
 A3: "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>" and
 A4: "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X))\<rfloor>" and
 A5: "\<lfloor>\<P> \<N>\<E>\<rfloor>" and
 B:  "\<lfloor>\<^bold>\<forall>\<phi>.(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>)\<rfloor>" (*Logic KB*)

lemma B': "\<forall>x y. \<not>(x\<^bold>ry) \<or> (y\<^bold>rx)" using B by fastforce

(*Necessary existence of a Godlike entity*)
theorem T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" 
proof -
 have T1: "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E X))\<rfloor>" 
          using A1 A2 by blast
 have T2: "\<lfloor>\<P> \<G>\<rfloor>" by (metis A3 G_def)
 have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using T1 T2 by simp
 have T4: "\<lfloor>\<^bold>\<forall>\<^sup>Ex.((\<G> x)\<^bold>\<rightarrow>(\<E> \<G> x))\<rfloor>" 
          by (metis A1 A4 G_def E_def)
 have T5: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E\<G>))\<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E\<G>)\<rfloor>" 
          by (smt A5 G_def B' NE_def T4)
 thus ?thesis using T3 by blast qed

(*Existence of a Godlike entity*)
lemma "\<lfloor>\<^bold>\<exists>\<^sup>E \<G>\<rfloor>" using A1 A2 B' T6 by blast

(*Consistency*) 
lemma True nitpick[satisfy] oops (*Model found*)

(*Modal collapse: holds*)
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>)\<rfloor>" 
proof - {fix w fix Q
 have 1: "\<forall>x.((\<G> x w) \<longrightarrow>
           (\<^bold>\<forall>Z.((Z x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez.((\<G> z) \<^bold>\<rightarrow> (Z z))))) w)" 
         by (metis A1 A4 G_def)
 have 2: "(\<exists>x. \<G> x w)\<longrightarrow>((Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez.((\<G> z) \<^bold>\<rightarrow> Q))) w)" 
         using 1 by force
 have 3: "(Q \<^bold>\<rightarrow> \<^bold>\<box>Q) w" using B' T6 2 by blast} 
 thus ?thesis by auto qed

(*Analysis of positive properties using ultrafilters*)
theorem U1: "\<lfloor>UFilter \<P>\<rfloor>" sledgehammer (*Proof found*)
proof - 
 have 1: "\<lfloor>(\<^bold>U\<^bold>\<in>\<P>) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<emptyset>\<^bold>\<in>\<P>)\<rfloor>" 
          using A1 A2 by blast
 have 2: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(((\<phi>\<^bold>\<in>\<P>)\<^bold>\<and>(\<phi>\<^bold>\<subseteq>\<psi>))\<^bold>\<rightarrow>(\<psi>\<^bold>\<in>\<P>))\<rfloor>" 
         by (smt A2 B' MC)
 have 3: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(((\<phi>\<^bold>\<in>\<P>)\<^bold>\<and>(\<psi>\<^bold>\<in>\<P>))\<^bold>\<rightarrow>((\<phi>\<^bold>\<sqinter>\<psi>)\<^bold>\<in>\<P>))\<rfloor>" 
         by (metis A1 A2 G_def B' T6)
 have 4: "\<lfloor>\<^bold>\<forall>\<phi>.((\<phi>\<^bold>\<in>\<P>) \<^bold>\<or> ((\<inverse>\<phi>)\<^bold>\<in>\<P>))\<rfloor>" 
         using A1 by blast
 thus ?thesis using 1 2 3 4 by simp qed

lemma L1: "\<lfloor>\<^bold>\<forall>X Y.((X\<Rrightarrow>Y) \<^bold>\<rightarrow> (X\<^bold>\<sqsubseteq>Y))\<rfloor>" 
          by (metis A1 A2 MC)
lemma L2: "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (X\<^bold>\<sqsubseteq>Y)) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" 
          by (smt A2 B' MC)

(*Set of supersets of X, we call this HF X*)
abbreviation HF where "HF X \<equiv> \<lambda>Y.(X\<^bold>\<sqsubseteq>Y)"

(*HF \<G> is a filter; hence, HF \<G> is Hauptfilter of \<G>*) 
lemma F1: "\<lfloor>Filter (HF \<G>)\<rfloor>" by (metis A2 B' T6 U1)
lemma F2: "\<lfloor>UFilter (HF \<G>)\<rfloor>" by (smt A1 F1 G_def)

(*T6 follows directly from F1*) 
theorem T6again: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using F1 by simp 
end




(*
(*The simplified version in appendix C is implied*) 
lemma  A1':  "\<lfloor>\<P>(\<lambda>x. x\<^bold>=x) \<^bold>\<and> \<^bold>\<not>\<P>(\<lambda>x. x\<^bold>\<noteq>x)\<rfloor>" using A1 A2 by blast
lemma A2'': "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X\<^bold>\<sqsubseteq>Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" by (metis A1 A2 B G_def T6)
lemma T2:   "\<lfloor>\<P> \<G>\<rfloor>" by (metis A3 G_def)
*)

(*
theorem T6again: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>"  
proof -
 have L1: "\<lfloor>(\<^bold>\<exists>X. \<P> X \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists>\<^sup>E X)) \<^bold>\<rightarrow> \<P>(\<lambda>x. x\<^bold>\<noteq>x)\<rfloor>" 
   by (metis A2 B G_def T6)
 have L2: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>X. \<P> X \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists>\<^sup>E X))\<rfloor>" 
   using A1 A2 L1 by blast 
 have T1': "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> (\<^bold>\<exists>\<^sup>E X)\<rfloor>" by (metis L2)  
 have T3': "\<lfloor>\<^bold>\<exists>\<^sup>E \<G>\<rfloor>"
   by (metis A2 A5 B L2 T6)
 have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" 
   using A1 A2 T3' by blast (*not needed*)
 have T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis T3') 
 thus ?thesis by simp qed
*)