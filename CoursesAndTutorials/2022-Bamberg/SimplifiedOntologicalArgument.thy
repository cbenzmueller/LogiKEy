theory SimplifiedOntologicalArgument      (*C. Benzmüller, 2021*)
  imports HOML
begin
(*Positive properties*) 
consts posProp::"\<gamma>\<Rightarrow>\<sigma>" ("\<P>")

(*Definition of Godlike*)
definition G ("\<G>") where "\<G>(x) \<equiv> \<^bold>\<forall>\<Phi>.(\<P>(\<Phi>) \<^bold>\<rightarrow> \<Phi>(x))"

(*Axiom's of new variant based on ultrafilters*) 
axiomatization where 
 CORO1: "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" and
 CORO2: "\<lfloor>\<^bold>\<forall>\<Phi> \<Psi>. \<P>(\<Phi>) \<^bold>\<and> (\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> \<P>(\<Psi>)\<rfloor>" and
 AXIOM3: "\<lfloor>\<P> \<G>\<rfloor>" 

(*Verifying the simplified ontological argument; version 1*)
lemma LEMMA1: "\<lfloor>(\<^bold>\<exists>\<Phi>.(\<P>(\<Phi>) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists>x. \<Phi>(x)))) \<^bold>\<rightarrow> \<P>(\<lambda>x.(x\<^bold>\<noteq>x))\<rfloor>" 
  by (meson CORO2)
lemma LEMMA2: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>\<Phi>.(\<P>(\<Phi>) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists>x. \<Phi>(x))))\<rfloor>" 
  using CORO1 LEMMA1 by blast
lemma LEMMA3: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<P>(\<Phi>) \<^bold>\<rightarrow> (\<^bold>\<exists>x. \<Phi>(x)))\<rfloor>" using LEMMA2 by blast
theorem THEOREM3': "\<lfloor>\<^bold>\<exists>x. \<G>(x)\<rfloor>" using AXIOM3 LEMMA3 by auto
theorem THEOREM3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" by (simp add: THEOREM3')
theorem CORO: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" nitpick oops (*countermodel*)

(*Modal Logic T*) 
axiomatization where T: "\<lfloor>\<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>" 
lemma T': "\<lfloor>\<^bold>\<forall>\<phi>. \<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<rfloor>" by (metis T)

(*Verifying the simplified ontological argument; version 2*) 
theorem THEOREM1: "\<lfloor>\<^bold>\<forall>\<Phi>. \<P>(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>x. \<Phi>(x))\<rfloor>" 
  by (metis CORO1 CORO2 T')
theorem CORO: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" using AXIOM3 THEOREM1 by auto
theorem THEOREM2: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. \<G>(x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" 
  by (meson AXIOM3 CORO1 CORO2)
theorem THEO3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" using CORO THEOREM2 by blast 
theorem THEO3': "\<lfloor>\<^bold>\<exists>x. \<G>(x)\<rfloor>" by (metis T THEO3)

lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>\<rfloor>" nitpick oops (*countermodel*)

(*Consistency*)
lemma True nitpick[satisfy,show_all,card=1,format=2] oops (*Model found*)
end


(*
(*Further Corollaries of Scott's theory*)
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>\<rfloor>" nitpick (*Modal collapse: holds*)
proof - {fix w fix Q
 have 1: "\<forall>x. \<G>(x)(w) \<longrightarrow> (\<^bold>\<forall>Z. Z(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>z. \<G>(z) \<^bold>\<rightarrow> Z(z)))(w)" 
         sledgehammer
 have 2: "(\<exists>x. \<G>(x)(w)) \<longrightarrow> (Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>z. (\<G> z) \<^bold>\<rightarrow> Q))(w)" 
        sledgehammer
 have 3: "(Q \<^bold>\<rightarrow> \<^bold>\<box>Q)(w)" sledgehammer
        } 
 thus ?thesis by auto qed
*)

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