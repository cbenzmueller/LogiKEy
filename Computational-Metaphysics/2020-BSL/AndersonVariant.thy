theory AndersonVariant imports IHOML ModalUltrafilter
begin
(**Positiveness**) consts positiveProperty::"\<gamma>\<Rightarrow>\<sigma>" ("\<P>")
(**Part I**)
 (*D1'*) definition GA::\<gamma> ("G\<^sup>A") where "G\<^sup>A x \<equiv> \<^bold>\<forall>Y::\<gamma>. \<P> Y \<^bold>\<leftrightarrow> \<^bold>\<box>(Y x)"
 (*A1a*) axiomatization where A1a:"\<lfloor>\<^bold>\<forall>X. \<P>(\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X)\<rfloor>" 
 (*A2*)  axiomatization where A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" 
 (*T1*)  theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A2 by metis
 (*T2*)  axiomatization where T2: "\<lfloor>\<P> G\<^sup>A\<rfloor>"  (*here we postulate T2 instead of proving it*)      
 (*T3*)  theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by (metis A1a A2 T2) 
(**Part II**)   
 (*Logic KB*) axiomatization where symm: "\<forall>x y. x r y \<longrightarrow> y r x"
 (*A4*)  axiomatization where A4: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"  
 (*D2'*) abbreviation essA::"\<gamma>\<Rightarrow>\<gamma>" ("\<E>\<^sup>A") where "\<E>\<^sup>A Y x \<equiv> \<^bold>\<forall>Z. \<^bold>\<box>(Z x) \<^bold>\<leftrightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. Y z \<^bold>\<rightarrow> Z z)"
 (*T4*)  theorem T4: "\<lfloor>\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)\<rfloor>" by (metis (mono_tags) A2 GA_def T2 symm) 
 (*D3*)  abbreviation NEA::\<gamma> ("NE\<^sup>A") where "NE\<^sup>A x  \<equiv> \<^bold>\<forall>Y. \<E>\<^sup>A Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y"
 (*A5*)  axiomatization where A5: "\<lfloor>\<P> NE\<^sup>A\<rfloor>"
 (*T5*)  theorem T5: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by (metis A2 GA_def T2 symm)
 (*T6*)  theorem T6: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>"  using T3 T5 by blast
(**Modal collapse**) lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[user_axioms,show_all] oops(*Countermodel*)
(**Consistency**) lemma True nitpick[satisfy,user_axioms] oops  (*Model found by Nitpick*)
(**Analysis of positive properties using ultrafilters**)
 (*U1*) theorem U1: "\<lfloor>\<gamma>-Ultrafilter \<P>\<rfloor>" nitpick[user_axioms,show_all] oops (*Countermodel*)
 (*U2*) abbreviation "\<P>' \<equiv> \<lambda>\<phi>.(\<P>\<^bold>\<down>\<phi>)" (*Set of \<phi>'s whose rigidly intens. extensions are positive*)
        theorem U2: "\<lfloor>\<gamma>-Ultrafilter \<P>'\<rfloor>"  (*Sledgehammer succeeds, reconstruction fails*)
          proof - have 1: "\<lfloor>\<^bold>U\<^sup>\<gamma>\<^bold>\<in>\<^sup>\<gamma>\<P>' \<^bold>\<and> \<^bold>\<not>\<^bold>\<emptyset>\<^sup>\<gamma>\<^bold>\<in>\<^sup>\<gamma>\<P>'\<rfloor>" using A2 T1 T2 by fastforce
                  have 2: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<gamma>\<P>' \<^bold>\<and> \<phi>\<^bold>\<subseteq>\<^sup>\<gamma>\<psi>) \<^bold>\<rightarrow> \<psi>\<^bold>\<in>\<^sup>\<gamma>\<P>'\<rfloor>" by (metis A2) 
                  have 3: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<gamma>\<P>' \<^bold>\<and> \<psi>\<^bold>\<in>\<^sup>\<gamma>\<P>') \<^bold>\<rightarrow> ((\<phi>\<^bold>\<sqinter>\<^sup>\<gamma>\<psi>)\<^bold>\<in>\<^sup>\<gamma>\<P>')\<rfloor>" by (smt GA_def T3 T5 symm)
                  have 4: "\<lfloor>\<^bold>\<forall>\<phi>. \<phi>\<^bold>\<in>\<^sup>\<gamma>\<P>' \<^bold>\<or> (\<inverse>\<^sup>\<gamma>\<phi>)\<^bold>\<in>\<^sup>\<gamma>\<P>'\<rfloor>"by (smt GA_def T3 T5 symm)
                  thus ?thesis by (simp add: 1 2 3 4) qed
 (*U3*) theorem U3: "\<lfloor>\<^bold>\<forall>\<phi>. \<phi>\<^bold>\<in>\<^sup>\<gamma>\<P>' \<^bold>\<leftrightarrow> \<phi>\<^bold>\<in>\<^sup>\<gamma>\<P>\<rfloor>" nitpick[user_axioms] oops(*Counterm.: \<P>',\<P> not equal*)
(**Modal logic S5: consistency and modal collapse**)
  axiomatization where refl: "\<forall>x. x r x" and trans: "\<forall>x y z. x r y \<and> y r z \<longrightarrow> x r z"
  lemma True nitpick[satisfy,user_axioms] oops  (*Model found by Nitpick*)
  lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[user_axioms] oops (*Countermodel*)
(**Barcan and converse Barcan formula for individuals (type e) and properties (type e\<Rightarrow>i\<Rightarrow>bool)**)
  lemma Bind1: "\<lfloor>(\<^bold>\<forall>\<^sup>Ex::e.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex::e. \<phi> x)\<rfloor>" nitpick[user_axioms] oops (*Countermodel*)
  lemma CBind1: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex::e. \<phi> x) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex::e.\<^bold>\<box>(\<phi> x))\<rfloor>" nitpick[user_axioms] oops (*Countermodel*)
  lemma Bpred1: "\<lfloor>(\<^bold>\<forall>x::e\<Rightarrow>i\<Rightarrow>bool. \<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x::e\<Rightarrow>i\<Rightarrow>bool. \<phi> x)\<rfloor>" by simp 
  lemma CBpred1: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x::e\<Rightarrow>i\<Rightarrow>bool. \<phi> x) \<^bold>\<rightarrow> (\<^bold>\<forall>x::e\<Rightarrow>i\<Rightarrow>bool. \<^bold>\<box>(\<phi> x))\<rfloor>" by simp
end 