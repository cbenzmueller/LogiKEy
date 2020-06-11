theory SimpleVariantSEinT imports HOML MFilter BaseDefs
begin
(*Axiom's of new variant based on ultrafilters*) 
axiomatization where 
 A1': "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" and
 A2'': "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (X\<^bold>\<sqsubseteq>Y)) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" and
 T2:   "\<lfloor>\<P> \<G>\<rfloor>" 

(*Modal Logic T*) 
axiomatization where T: "\<lfloor>\<^bold>\<forall>\<phi>.((\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> \<phi>)\<rfloor>" 
lemma T': "\<lfloor>\<^bold>\<forall>\<phi>.(\<phi> \<^bold>\<rightarrow> (\<^bold>\<diamond>\<phi>))\<rfloor>" by (metis T)

(*Necessary existence of a Godlike entity*) 
theorem T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" sledgehammer (*Proof found*)
proof -
 have T1: "\<lfloor>\<^bold>\<forall>X.((\<P> X)\<^bold>\<rightarrow>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E X)))\<rfloor>" by (metis A1' A2'' T') 
 have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis T1 T2)
 have T5: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis A1' A2'' T2) 
 thus ?thesis using T3 by simp qed

(*T6 again, with an alternative, simpler proof*) 
theorem T6again: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>"  
proof -
 have L1: "\<lfloor>(\<^bold>\<exists>X.((\<P> X)\<^bold>\<and>\<^bold>\<not>(\<^bold>\<exists>\<^sup>EX)))\<^bold>\<rightarrow>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" 
          by (smt A2'') 
 have L2: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>X.((\<P> X) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists>\<^sup>E X)))\<rfloor>" by (metis L1 A1')
 have T1': "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> (\<^bold>\<exists>\<^sup>E X))\<rfloor>" by (metis L2)  
 have T3': "\<lfloor>\<^bold>\<exists>\<^sup>E \<G>\<rfloor>" by (metis T1' T2)
 have L3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis T3' T') (*not needed*)
 thus ?thesis using T3' by simp qed
end



(*


(*Positive Properties as a Hauptfilter*)

(*unimportant*) declare [[smt_solver = cvc4, smt_oracle]]

(*Let CP denote the conjunction of all positive properties*)
consts CP::\<gamma>
axiomatization 
  where axCP: "\<lfloor>\<^bold>\<forall>\<^sup>Eu. CP u \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> Y u)\<rfloor>"

(*Definition of Hauptfilter for X*)
abbreviation HF::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)" ("\<H>\<F>") where "\<H>\<F> X \<equiv> \<lambda>Y.(X\<^bold>\<sqsubseteq>Y)"

(*The Hauptfilter of CP is a Filter*) 
lemma H1: "\<lfloor>Filter (\<H>\<F> CP)\<rfloor>" by (metis G_def A1' A2'' T2 axCP)

(*The Hauptfilter of CP is not an Ultrafilter*) 
lemma "\<lfloor>Ultrafilter (\<H>\<F> CP)\<rfloor>" nitpick oops (*Countermodel*)

(*Maximality of \<P> implies (\<H>\<F> CP) is an Ultrafilter*)
axiomatization where maxP: "\<lfloor>\<^bold>\<forall>\<phi>. (\<phi>\<^bold>\<in>\<P>) \<^bold>\<or> ((\<inverse>\<phi>)\<^bold>\<in>\<P>)\<rfloor>" 
lemma "\<lfloor>Ultrafilter (\<H>\<F> CP)\<rfloor>" by (smt axCP H1 T maxP)

end


(*
lemma MTL: "\<lfloor>\<^bold>\<forall>x y. \<G> x \<^bold>\<and> \<G> y \<^bold>\<rightarrow> (\<^bold>\<forall>P. P x \<^bold>\<rightarrow> P y)\<rfloor>" nitpick oops (*Cntm.*)
(*Gödel's A1, A4, A5: not implied anymore*)
lemma A1: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<leftrightarrow> \<P>(\<^bold>\<rightharpoondown>X)\<rfloor>" nitpick oops (*Counterm.*)
lemma A4: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>" nitpick oops (*Countermodel*)
definition ess("\<E>") where "\<E> Y x \<equiv> Y x \<^bold>\<and> (\<^bold>\<forall>Z. Z x \<^bold>\<rightarrow> (Y\<Rrightarrow>Z))" 
definition NE("\<N>\<E>") where "\<N>\<E> x \<equiv> \<lambda>w.(\<^bold>\<forall>Y. \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w"
lemma A5: "\<lfloor>\<P> \<N>\<E>\<rfloor>" nitpick oops (*Countermodel*)
lemma MT: "\<lfloor>\<^bold>\<forall>x y. \<G> x \<^bold>\<and> \<G> y \<^bold>\<rightarrow> x \<^bold>= y\<rfloor>" nitpick oops (*Cntm.*)
theorem F1: "\<lfloor>Filter \<P>\<rfloor>" sledgehammer oops (*Proof found*)
theorem U1: "\<lfloor>Ultrafilter \<P>\<rfloor>" nitpick oops (*Countermodel*)
end
*)



(*
(*Further Tests*)
 lemma A3': "\<lfloor>\<^bold>\<forall>X Y.((\<P> X) \<^bold>\<and> (\<P> Y)) \<^bold>\<rightarrow> \<P> (\<lambda>z. X z  \<^bold>\<and> Y z)\<rfloor>" sledgehammer(A3) nitpick oops

 lemma "\<lfloor>(X\<^bold>\<sqsubseteq>Y)\<^bold>\<rightarrow>(X\<Rrightarrow>Y)\<rfloor>" nitpick oops (*Countermodel*)
 lemma "\<lfloor>(X\<Rrightarrow>Y)\<^bold>\<rightarrow>(X\<^bold>\<sqsubseteq>Y)\<rfloor>" sledgehammer nitpick oops (*Countermodel*)
 lemma "(\<lfloor>(X\<^bold>\<sqsubseteq>Y)\<rfloor>)\<longrightarrow>(\<lfloor>(X\<Rrightarrow>Y)\<rfloor>)" nitpick oops (*Countermodel*)
 lemma "(\<lfloor>(X\<Rrightarrow>Y)\<rfloor>)\<longrightarrow>(\<lfloor>(X\<^bold>\<sqsubseteq>Y)\<rfloor>)" nitpick oops (*Countermodel*)
*)

(*
 consts Godlike::\<gamma>  NeEx::\<gamma>
 axiomatization where 
  1: "Godlike = G" and 
  2: "NeEx = NE"
 lemma True nitpick[satisfy] oops 
 lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[format=8] oops (*Countermodel*)
 lemma A1: "\<lfloor>\<^bold>\<forall>X.(\<^bold>\<not>(\<P> X) \<^bold>\<leftrightarrow> \<P>(\<^bold>\<rightharpoondown>X))\<rfloor>" nitpick[format=4] oops (*Countermodel*)
 lemma A4: "\<lfloor>\<forall>X.(\<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X))\<rfloor>" nitpick[format=4] oops (*Countermodel*)
 lemma A5: "\<lfloor>\<P> NE\<rfloor>" nitpick oops (*Countermodel*)
*)
*)