theory SimpleVariant imports HOML MFilter BaseDefs
begin
(*Axiom's of new, simplified variant*) 
axiomatization where 
 A1': "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" and 
 A2': "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> ((X\<^bold>\<sqsubseteq>Y) \<^bold>\<or> (X\<Rrightarrow>Y))) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" and
 A3:  "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>" 

lemma T2: "\<lfloor>\<P> \<G>\<rfloor>" by (metis A3 G_def) (*From A3*)
lemma L1: "\<lfloor>\<P>(\<lambda>x.(x\<^bold>=x))\<rfloor>" by (metis A2' A3) 

(*Necessary existence of a Godlike entity*) 
theorem T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" sledgehammer (*Proof found*)
proof -
 have T1: "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E X))\<rfloor>" by (metis A1' A2') 
 have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using T1 T2 by simp
 have T5: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis A1' A2' T2)
  thus ?thesis using T3 by blast qed

lemma True nitpick[satisfy] oops (*Consistency: model found*)

(*Modal collapse and monotheism: not implied*)
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>)\<rfloor>" nitpick oops (*Countermodel*)
lemma MT: "\<lfloor>\<^bold>\<forall>x y.(((\<G> x) \<^bold>\<and> (\<G> y)) \<^bold>\<rightarrow> (x\<^bold>=y))\<rfloor>" 
          nitpick oops (*Countermodel*)

(*Gödel's A1, A4, A5: not implied anymore*)
lemma A1: "\<lfloor>\<^bold>\<forall>X.((\<^bold>\<not>(\<P> X))\<^bold>\<leftrightarrow>(\<P>(\<^bold>\<rightharpoondown>X)))\<rfloor>" nitpick oops (*Ctm*)
lemma A4: "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X))\<rfloor>" nitpick oops (*Ctm*)
lemma A5: "\<lfloor>\<P> \<N>\<E>\<rfloor>" nitpick oops (*Countermodel*)

(*Checking filter and ultrafilter properties*) 
theorem F1: "\<lfloor>Filter \<P>\<rfloor>" sledgehammer oops (*Proof found*)
theorem U1: "\<lfloor>UFilter \<P>\<rfloor>" nitpick oops (*Countermodel*)
end


(*
(*More detailed proof for T5*)
theorem T5again: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" 
 proof -
 have L1: "\<lfloor>(\<^bold>\<exists>X.((\<P> X)\<^bold>\<and>\<^bold>\<not>(\<^bold>\<exists>\<^sup>EX)))\<^bold>\<rightarrow>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" by (smt A2') 
 have L2: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>X.((\<P> X) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists>\<^sup>E X)))\<rfloor>" by (metis L1 A1')
 have T1': "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> (\<^bold>\<exists>\<^sup>E X))\<rfloor>" by (metis L2)  
 have T2': "\<lfloor>\<P> \<G>\<rfloor>" by (metis A3 G_def)
 have T3': "\<lfloor>\<^bold>\<exists>\<^sup>E \<G>\<rfloor>" by (metis T1' T2')
 have L3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using T3' by auto
 have L4: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using L3 by blast
   thus ?thesis by blast qed
end 
*)

(*
lemma T: "\<lfloor>\<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>" sledgehammer nitpick oops
abbreviation h1 (infix"\<^bold>=\<^bold>="90) where "x\<^bold>=\<^bold>=y \<equiv> \<lambda>w.(x=y)"
abbreviation h2 (infix"\<^bold>\<noteq>\<^bold>\<noteq>"90) where "x\<^bold>\<noteq>\<^bold>\<noteq>y \<equiv> \<lambda>w.(x\<noteq>y)"

consts GG::\<gamma>
axiomatization where GG: "GG = \<G>" 

(*Definition Schnitt aller positiven Eigenschaften*)
abbreviation schnittPos::"\<gamma>\<Rightarrow>\<sigma>" ("SchnittPos") where "SchnittPos X \<equiv> X\<Sqinter>\<P>"

theorem  "\<lfloor>\<^bold>\<forall>X. (SchnittPos X) \<^bold>\<rightarrow> (X \<^bold>=\<^bold>= \<G>)\<rfloor>" nitpick[show_all,format=4] oops (*Countermodel*)


(*Definition of Hauptfilter for X*)
abbreviation hf::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)" ("Hauptfilter") 
  where "Hauptfilter X \<equiv> \<lambda>Y. (X\<^bold>\<subseteq>Y)"

abbreviation hf2::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)" ("Hauptfilter2") 
  where "Hauptfilter2 X \<equiv> \<lambda>Y. X\<^bold>\<sqsubseteq>Y"

abbreviation hf3::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)" ("Hauptfilter3") 
  where "Hauptfilter3 X \<equiv> \<lambda>Y. X\<Rrightarrow>Y"

abbreviation hf4::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)" ("Hauptfilter4") 
  where "Hauptfilter4 X \<equiv> \<lambda>Y. X\<^bold>\<sqsubseteq>Y \<^bold>\<or> X\<Rrightarrow>Y"

axiomatization where OneWorld: "\<exists>w::i. \<forall>v. w = v"

theorem H1: "\<lfloor>\<^bold>\<forall>X. (SchnittPos X) \<^bold>\<rightarrow> Filter (Hauptfilter X)\<rfloor>" 
  by (metis A1' A2' G_def T2) 

theorem H2: "\<lfloor>\<^bold>\<forall>X. (SchnittPos X) \<^bold>\<rightarrow> Filter (Hauptfilter2 X)\<rfloor>" 
  by (metis A1' A2' G_def T2) 

theorem H3: "\<lfloor>\<^bold>\<forall>X. (SchnittPos X) \<^bold>\<rightarrow> Filter (Hauptfilter3 X)\<rfloor>" 
  sledgehammer (A1' A2' G_def T2 OneWorld)
  by (smt A1' A2' G_def OneWorld T2)  nitpick oops (*Countermodel*)

theorem H4: "\<lfloor>\<^bold>\<forall>X. (SchnittPos X) \<^bold>\<rightarrow> Filter (Hauptfilter4 X)\<rfloor>" 
  proof - {fix X
  have 1: "\<lfloor>(SchnittPos X) \<^bold>\<rightarrow> (\<^bold>U\<^bold>\<in>(Hauptfilter4 X) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<emptyset>\<^bold>\<in>(Hauptfilter4 X)))\<rfloor>" 
    by (metis A1' A2' G_def T2 T6) 
  have 2: "\<lfloor>(SchnittPos X) \<^bold>\<rightarrow> (\<^bold>\<forall>\<phi> \<psi>.((\<phi>\<^bold>\<in>(Hauptfilter4 X) \<^bold>\<and> (\<phi>\<^bold>\<subseteq>\<psi>)) \<^bold>\<rightarrow> \<psi>\<^bold>\<in>(Hauptfilter4 X)))\<rfloor>"
    sledgehammer nitpick sorry  
  have 3: "\<lfloor>(SchnittPos X) \<^bold>\<rightarrow> (\<^bold>\<forall>\<phi> \<psi>.((\<phi>\<^bold>\<in>(Hauptfilter4 X) \<^bold>\<and> \<psi>\<^bold>\<in>(Hauptfilter4 X)) \<^bold>\<rightarrow> (\<phi>\<^bold>\<sqinter>\<psi>)\<^bold>\<in>(Hauptfilter4 X)))\<rfloor>"
     sorry 
  have 4: "\<lfloor>(SchnittPos X) \<^bold>\<rightarrow> Filter (Hauptfilter4 X)\<rfloor>" 
    using 1 2 3 sorry
}
  thus ?thesis sorry qed


consts HF1::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)" HF2::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)" HF3::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)" HF4::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)" 



axiomatization where 
 AA1:  "HF1 = Hauptfilter" and
 AA2:  "HF2 = Hauptfilter2" and
 AA3:  "HF3 = Hauptfilter3" and
 AA4:  "HF4 = Hauptfilter4"

theorem  "\<lfloor>\<^bold>\<forall>X. (SchnittPos X) \<^bold>\<rightarrow> ((HF1 X) \<^bold>=\<^bold>= (HF2 X))\<rfloor>" sledgehammer nitpick[show_all,format=4] oops
theorem  "\<lfloor>\<^bold>\<forall>X. (SchnittPos X) \<^bold>\<rightarrow> ((HF1 X) \<^bold>=\<^bold>= (HF3 X))\<rfloor>" sledgehammer nitpick[show_all,format=4] oops
theorem  "\<lfloor>\<^bold>\<forall>X. (SchnittPos X) \<^bold>\<rightarrow> ((HF2 X) \<^bold>=\<^bold>= (HF3 X))\<rfloor>" sledgehammer nitpick[show_all,format=4] oops
theorem  "\<lfloor>\<^bold>\<forall>X. (SchnittPos X) \<^bold>\<rightarrow> ((HF3 X) \<^bold>=\<^bold>= (HF4 X))\<rfloor>" sledgehammer nitpick[show_all,format=4] oops





(*Necessary existence of a Godlike entity*) 
theorem T6':  "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" sledgehammer (*Proof found*)
 proof -
  have T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E X)\<rfloor>" by (metis A1' A2') 
  have T2: "\<lfloor>\<P> \<G>\<rfloor>" by (metis A3 G_def)
  have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using T1 T2 by simp
  have T5: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis A1' A2' T2)
  thus ?thesis using T3 by blast qed

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