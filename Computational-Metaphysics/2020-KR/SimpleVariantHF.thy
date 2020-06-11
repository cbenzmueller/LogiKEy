theory SimpleVariantHF imports HOML MFilter BaseDefs
begin
(*Definition: Set of supersets of X, we call this \<H>\<F> X*)
abbreviation HF::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)"  where "HF X \<equiv> \<lambda>Y.(X\<^bold>\<sqsubseteq>Y)"

(*Postulate: \<H>\<F> \<G> is a filter; i.e., Hauptfilter of \<G>*) 
axiomatization where F1: "\<lfloor>Filter (HF \<G>)\<rfloor>" 

(*Necessary existence of a Godlike entity*) 
theorem T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using F1 by auto (*Proof found*)

theorem T6again: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>"  
proof -
 have T3': "\<lfloor>\<^bold>\<exists>\<^sup>E \<G>\<rfloor>" using F1 by auto
 have T6:  "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using T3' by blast 
 thus ?thesis by simp qed

(*Possible existence of Godlike entity not implied*)
lemma T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" nitpick oops (*Countermodel*)

(*Axiom T enforces possible existence of Godlike entity*)
axiomatization 
lemma T3: assumes T: "\<lfloor>\<^bold>\<forall>\<phi>.((\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> \<phi>)\<rfloor>"
          shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>"     using F1 T by auto

lemma True nitpick[satisfy] oops (*Consistency*)

(*Modal collapse: not implied anymore*)
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>)\<rfloor>" nitpick oops (*Countermodel*)
lemma MT: "\<lfloor>\<^bold>\<forall>x y.(((\<G> x) \<^bold>\<and> (\<G> y)) \<^bold>\<rightarrow> (x\<^bold>=y))\<rfloor>" 
          nitpick oops (*Countermodel*)
end

