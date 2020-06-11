theory SimpleVariantSE imports HOML MFilter BaseDefs
begin
(*Axiom's of new variant based on ultrafilters*) 
axiomatization where 
 A1': "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" and
 A2'': "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (X\<^bold>\<sqsubseteq>Y)) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" and
 T2:  "\<lfloor>\<P> \<G>\<rfloor>" 

(*Necessary existence of a Godlike entity*) 
theorem T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using A1' A2'' T2 by blast 
theorem T7: "\<lfloor>\<^bold>\<exists>\<^sup>E \<G>\<rfloor>" using A1' A2'' T2 by blast 

(*Possible existence of a Godlike: has counterodel*) 
lemma T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" nitpick oops (*Counterodel*)

lemma T3': assumes T: "\<lfloor>\<^bold>\<forall>\<phi>.((\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> \<phi>)\<rfloor>" 
           shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" 
           using A1' A2'' T2 T by metis
end


(*
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