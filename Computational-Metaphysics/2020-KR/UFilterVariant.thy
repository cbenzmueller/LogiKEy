theory UFilterVariant imports HOML MFilter BaseDefs
begin
(*Axiom's of ultrafilter variant*) 
axiomatization where 
 U1: "\<lfloor>UFilter \<P>\<rfloor>" and
 A2: "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (X\<Rrightarrow>Y)) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" and
 A3: "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>" 

(*Necessary existence of a Godlike entity*) 
theorem T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" sledgehammer (*Proof found*)
proof -
 have T1: "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E X))\<rfloor>" by (metis A2 U1) 
 have T2: "\<lfloor>\<P> \<G>\<rfloor>" by (metis A3 G_def)
 have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using T1 T2 by simp
 have T5: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" 
          by (metis A2 G_def T2 U1)
 thus ?thesis using T3 by blast qed

(*Consistency*) 
lemma True nitpick[satisfy] oops  (*Model found*)

(*Modal collapse*)
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>)\<rfloor>" nitpick oops (*Countermodel*)
end



(*
 definition ess ("\<E>") where "\<E> Y x \<equiv> Y x \<^bold>\<and> (\<^bold>\<forall>Z.(Z x \<^bold>\<rightarrow> (Y\<Rrightarrow>Z)))" 
 definition NE ("NE") where "NE x \<equiv> \<lambda>w.((\<^bold>\<forall>Y.(\<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y)) w)"
 consts Godlike::\<gamma> UltraFilter::"(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" NeEx::\<gamma>
 axiomatization where 
  1: "Godlike = G" and 
  2: "UltraFilter = Ultrafilter" and
  3: "NeEx = NE"
 lemma True nitpick[satisfy] oops 
 lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>\<rfloor>" nitpick[format=8] oops (*Countermodel*)
 lemma A1: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<leftrightarrow> \<P>(\<^bold>\<rightharpoondown>X)\<rfloor>" using U1 by fastforce
 lemma A4: "\<lfloor>(\<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X))\<rfloor>" nitpick [format=4] oops (*Countermodel*)
 lemma A5: "\<lfloor>\<P> NE\<rfloor>" nitpick oops (*Countermodel*)
*)