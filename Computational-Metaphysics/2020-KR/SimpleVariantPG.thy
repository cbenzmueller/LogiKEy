theory SimpleVariantPG imports HOML MFilter BaseDefs
begin
(*Axiom's of simplified variant with A3 replaced*) 
axiomatization where 
 A1': "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" and
 A2': "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> ((X\<^bold>\<sqsubseteq>Y)\<^bold>\<or>(X\<Rrightarrow>Y))) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" and
 T2:  "\<lfloor>\<P> \<G>\<rfloor>"

(*Necessary existence of a Godlike entity*) 
theorem T6:  "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" sledgehammer (*Proof found*)
proof -
 have T1: "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E X))\<rfloor>" by (metis A1' A2') 
 have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using T1 T2 by simp
 have T5: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis A1' A2' T2)
 thus ?thesis using T3 by blast qed
 
lemma True nitpick[satisfy] oops (*Consistency: model found*)

(*Modal collapse and Monotheism: not implied*)
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>)\<rfloor>" nitpick oops (*Countermodel*)
lemma MT: "\<lfloor>\<^bold>\<forall>x y.(((\<G> x)\<^bold>\<and>(\<G> y))\<^bold>\<rightarrow>(x\<^bold>=y))\<rfloor>" 
          nitpick oops (*Countermodel*)
end


(*
lemma A3':  "\<lfloor>\<^bold>\<forall>\<Z>. \<P>\<o>\<s> \<Z> \<^bold>\<rightarrow> (\<^bold>\<forall>X. (X\<Sqinter>\<Z>) \<^bold>\<rightarrow> \<P> X)\<rfloor>" 
  nitpick sledgehammer oops


(*Gödel's A1, A4, A5: not implied anymore*)
lemma A1: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<leftrightarrow> \<P>(\<^bold>\<rightharpoondown>X)\<rfloor>" nitpick oops (*Counterm.*)
lemma A4: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>" nitpick oops (*Countermodel*)
definition ess("\<E>") where "\<E> Y x \<equiv> Y x \<^bold>\<and> (\<^bold>\<forall>Z. Z x \<^bold>\<rightarrow> (Y\<Rrightarrow>Z))" 
definition NE("\<N>\<E>") where "\<N>\<E> x \<equiv> \<lambda>w.(\<^bold>\<forall>Y. \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w"
lemma A5: "\<lfloor>\<P> \<N>\<E>\<rfloor>" nitpick oops (*Countermodel*)
lemma MT: "\<lfloor>\<^bold>\<forall>x y. \<G> x \<^bold>\<and> \<G> y \<^bold>\<rightarrow> x \<^bold>= y\<rfloor>" nitpick oops (*Cntm.*)
lemma T2: "\<lfloor>\<P> \<G>\<rfloor>" by (metis A3 G_def)
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
lemma T2: "\<lfloor>\<P> \<G>\<rfloor>" by (metis A3 G_def)
theorem F1: "\<lfloor>Filter \<P>\<rfloor>" sledgehammer (*Proof found*)
proof - 
 have 1: "\<lfloor>\<^bold>U\<^bold>\<in>\<P> \<^bold>\<and> \<^bold>\<not>(\<^bold>\<emptyset>\<^bold>\<in>\<P>)\<rfloor>" using A1' by auto
 have 2: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.((\<phi>\<^bold>\<in>\<P> \<^bold>\<and> (\<phi>\<^bold>\<subseteq>\<psi>)) \<^bold>\<rightarrow> \<psi>\<^bold>\<in>\<P>)\<rfloor>" by (metis A2')
 have 3: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.((\<phi>\<^bold>\<in>\<P> \<^bold>\<and> \<psi>\<^bold>\<in>\<P>) \<^bold>\<rightarrow> (\<phi>\<^bold>\<sqinter>\<psi>)\<^bold>\<in>\<P>)\<rfloor>" by (metis (no_types, lifting) A2' G_def A3) 
 thus ?thesis using 1 2 3 by simp qed

theorem U1: "\<lfloor>Ultrafilter \<P>\<rfloor>" nitpick oops (*Countermodel*)
*)

(*
abbreviation a2::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (infix"\<^bold>\<in>"81) where "x\<^bold>\<in>S \<equiv> S x"
abbreviation b2::\<gamma> ("\<^bold>\<emptyset>") where "\<^bold>\<emptyset> \<equiv> \<lambda>x. \<^bold>\<bottom>"  
abbreviation c2::\<gamma> ("\<^bold>U") where "\<^bold>U \<equiv> \<lambda>x. \<^bold>\<top>"
abbreviation d2::"\<gamma>\<Rightarrow>\<gamma>\<Rightarrow>\<sigma>" ("_\<^bold>\<subseteq>_") where "\<phi>\<^bold>\<subseteq>\<psi> \<equiv> \<^bold>\<forall>x. \<phi> x \<^bold>\<rightarrow> \<psi> x"
abbreviation e2::"\<gamma>\<Rightarrow>\<gamma>\<Rightarrow>\<gamma>" ("_\<^bold>\<sqinter>_") where "\<phi>\<^bold>\<sqinter>\<psi> \<equiv> \<lambda>x. \<phi> x \<^bold>\<and> \<psi> x"
abbreviation f2::"\<gamma>\<Rightarrow>\<gamma>" ("\<inverse>_") where "\<inverse>\<psi> \<equiv> \<lambda>x. \<^bold>\<not>(\<psi> x)"  

(*Definition of modal filter*)
abbreviation g::"(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("Filter") 
  where "Filter \<Phi> \<equiv> \<^bold>U\<^bold>\<in>\<Phi> \<^bold>\<and> \<^bold>\<not>(\<^bold>\<emptyset>\<^bold>\<in>\<Phi>)
                     \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>. (\<phi>\<^bold>\<in>\<Phi> \<^bold>\<and> (\<phi>\<^bold>\<subseteq>\<psi>)) \<^bold>\<rightarrow> \<psi>\<^bold>\<in>\<Phi>)
                     \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>. (\<phi>\<^bold>\<in>\<Phi> \<^bold>\<and> \<psi>\<^bold>\<in>\<Phi>) \<^bold>\<rightarrow> (\<phi>\<^bold>\<sqinter>\<psi>)\<^bold>\<in>\<Phi>)"

(*Definition of modal ultrafilter *)
abbreviation h::"(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("Ultrafilter")
  where "Ultrafilter \<Phi> \<equiv> Filter \<Phi> \<^bold>\<and> (\<^bold>\<forall>\<phi>. (\<phi>\<^bold>\<in>\<Phi>) \<^bold>\<or> ((\<inverse>\<phi>)\<^bold>\<in>\<Phi>))"

theorem U1: "\<lfloor>Ultrafilter \<P>\<rfloor>"
proof - 
 have 1: "\<lfloor>\<^bold>U\<^bold>\<in>\<P> \<^bold>\<and> \<^bold>\<not>(\<^bold>\<emptyset>\<^bold>\<in>\<P>)\<rfloor>" using A1' by auto
 have 2: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.((\<phi>\<^bold>\<in>\<P> \<^bold>\<and> (\<phi>\<^bold>\<subseteq>\<psi>)) \<^bold>\<rightarrow> \<psi>\<^bold>\<in>\<P>)\<rfloor>" by (metis A2')
 have 3: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.((\<phi>\<^bold>\<in>\<P> \<^bold>\<and> \<psi>\<^bold>\<in>\<P>) \<^bold>\<rightarrow> (\<phi>\<^bold>\<sqinter>\<psi>)\<^bold>\<in>\<P>)\<rfloor>" using A3 sledgehammer [remote_satallax remote_leo2 remote_leo3]  nitpick sorry
 have 4: "\<lfloor>\<^bold>\<forall>\<phi>.(\<phi>\<^bold>\<in>\<P> \<^bold>\<or> (\<inverse>\<phi>)\<^bold>\<in>\<P>)\<rfloor>" nitpick oops
 thus ?thesis using 1 2 3 4 by simp qed

 lemma "\<lfloor>Filter \<P> \<rfloor>" sledgehammer nitpick oops (*Counterm*)
 lemma "\<lfloor>Ultrafilter \<P> \<rfloor>" sledgehammer nitpick oops (*Counterm*)

(*Filter and ultrafilter are consistent*)

 consts Godlike::\<gamma>  NeEx::\<gamma> 
 axiomatization where 
  1: "Godlike = \<G>" and 
  2: "NeEx = \<N>\<E>" and
  3: "\<exists>e1::e. \<exists>e2::e. \<not> e1 = e2" 

 lemma True nitpick[satisfy] oops
 lemma MT: "\<lfloor>\<^bold>\<forall>x y. \<G> x \<^bold>\<and> \<G> y \<^bold>\<rightarrow> x \<^bold>= y\<rfloor>" nitpick oops (*Cntm.*)
 lemma MT: "\<lfloor>\<^bold>\<forall>\<^sup>Ex y. \<G> x \<^bold>\<and> \<G> y \<^bold>\<rightarrow> x \<^bold>= y\<rfloor>" sledgehammer nitpick [format=2] oops
 lemma MT': "\<G> x w \<and> \<G> y w \<and> \<not>\<G> z w \<longrightarrow> x = y" sledgehammer nitpick [format=2] oops
 lemma MT'': "\<lfloor>\<^bold>\<forall>\<^sup>Ex y. \<G> x \<^bold>\<and> \<G> y \<^bold>\<rightarrow> (\<^bold>\<forall>P. P x \<^bold>\<rightarrow> P y)\<rfloor>" sledgehammer nitpick [format=2] oops
 lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[timeout = 10000] nunchaku oops (*Countermodel*)
 lemma A1: "\<lfloor>\<^bold>\<forall>X.(\<^bold>\<not>(\<P> X) \<^bold>\<leftrightarrow> \<P>(\<^bold>\<rightharpoondown>X))\<rfloor>" nitpick[format=4] oops (*Countermodel*)
 lemma A4: "\<lfloor>\<^bold>\<forall>X.(\<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X))\<rfloor>" nitpick[format=4] oops (*Countermodel*)
 lemma A5: "\<lfloor>\<P> \<N>\<E>\<rfloor>" nitpick oops (*Countermodel*)
*)