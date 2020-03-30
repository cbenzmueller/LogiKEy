theory ScottVariant imports IHOML ModalUltrafilter
begin                         
(**Positiveness**) consts positiveProperty::"\<gamma>\<Rightarrow>\<sigma>" ("\<P>") 
(**Part I**)
 (*D1*) definition G::\<gamma> ("G") where "G x \<equiv> \<^bold>\<forall>Y::\<gamma>. \<P> Y \<^bold>\<rightarrow> Y x"
 (*A1*) axiomatization where A1a: "\<lfloor>\<^bold>\<forall>X. \<P>(\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X)\<rfloor>" and A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<^bold>\<rightharpoondown>X)\<rfloor>" and
 (*A2*) A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and   
 (*A3*) A3: "\<lfloor>\<^bold>\<forall>Z X. ((\<^bold>\<forall>Y. Z Y \<^bold>\<rightarrow> \<P> Y) \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>x. X x \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. Z Y \<^bold>\<rightarrow> Y x))) \<^bold>\<rightarrow> \<P> X\<rfloor>" 
 (*T1*) theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" by (metis A1a A2)
 (*T2*) theorem T2: "\<lfloor>\<P> G\<rfloor>" by (smt A3 G_def) 
 (*T3*) theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<rfloor>" using T1 T2 by simp 
(**Part II**)
 (*Logic KB*)  axiomatization where symm: "\<forall>x y. x r y \<longrightarrow> y r x"
 (*A4*) axiomatization where A4: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"      
 (*D2*) definition ess::"\<gamma>\<Rightarrow>\<gamma>" ("\<E>") where  "\<E> Y x \<equiv> Y x \<^bold>\<and> (\<^bold>\<forall>Z. Z x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. Y z \<^bold>\<rightarrow>  Z z))"   
 (*T4*) theorem T4: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<E> G x)\<rfloor>" by (metis A1b A4 G_def ess_def)
 (*D3*) definition NE::\<gamma> ("NE") where "NE x \<equiv> \<^bold>\<forall>Y. \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y"
 (*A5*) axiomatization where A5: "\<lfloor>\<P> NE\<rfloor>"
 (*T5*) theorem T5: "\<lfloor>(\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" by (metis A5 G_def NE_def T4 symm) 
 (*T6*) theorem T6: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using T3 T5 by blast
(**Consistency**) lemma True nitpick[satisfy,user_axioms] oops  (*Model found by Nitpick*)
(**Modal collapse**)
  lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" 
    proof - {fix w fix Q
      have "\<forall>x. G x w \<longrightarrow> (\<^bold>\<forall>Z. Z x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> Z z)) w" by (metis A1b A4 G_def)
      hence 1: "(\<exists>x. G x w) \<longrightarrow> ((Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> Q)) w)" by force
      have "\<exists>x. G x w" using T3 T6 symm by blast
      hence "(Q \<^bold>\<rightarrow> \<^bold>\<box>Q) w" using 1 T6 by blast} 
    thus ?thesis by auto qed
(**Analysis of positive properties using ultrafilters**)
 (*unimportant*) declare [[smt_solver = cvc4, smt_oracle]]
 (*U1*) theorem U1: "\<lfloor>\<gamma>-Ultrafilter \<P>\<rfloor>" (*Sledgehammer succeeds, reconstruction fails*)
          proof - have 1: "\<lfloor>\<^bold>U\<^sup>\<gamma>\<^bold>\<in>\<^sup>\<gamma>\<P> \<^bold>\<and> \<^bold>\<not>\<^bold>\<emptyset>\<^sup>\<gamma>\<^bold>\<in>\<^sup>\<gamma>\<P>\<rfloor>" using A1b T1 by auto 
                  have 2: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<gamma>\<P> \<^bold>\<and> \<phi>\<^bold>\<subseteq>\<^sup>\<gamma>\<psi>) \<^bold>\<rightarrow> \<psi>\<^bold>\<in>\<^sup>\<gamma>\<P>\<rfloor>" by (metis A1b G_def T1 T6 symm)
                  have 3: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<gamma>\<P> \<^bold>\<and> \<psi>\<^bold>\<in>\<^sup>\<gamma>\<P>) \<^bold>\<rightarrow> ((\<phi>\<^bold>\<sqinter>\<^sup>\<gamma>\<psi>)\<^bold>\<in>\<^sup>\<gamma>\<P>)\<rfloor>" by (metis A1b G_def T1 T6 symm)
                  have 4: "\<lfloor>\<^bold>\<forall>\<phi>. \<phi>\<^bold>\<in>\<^sup>\<gamma>\<P> \<^bold>\<or> (\<inverse>\<^sup>\<gamma>\<phi>)\<^bold>\<in>\<^sup>\<gamma>\<P>\<rfloor>" using A1b by blast
                  thus ?thesis by (simp add: 1 2 3 4) qed
 (*U2*) abbreviation "\<P>' \<equiv> \<lambda>\<phi>.(\<P>\<^bold>\<down>\<phi>)" (*Set of \<phi>'s whose rigidly intens. extensions are positive*)
theorem U2: "\<lfloor>\<gamma>-Ultrafilter \<P>'\<rfloor>"  (*Sledgehammer succeeds, reconstruction fails*)
          proof - have 1: "\<lfloor>\<^bold>U\<^sup>\<gamma>\<^bold>\<in>\<^sup>\<gamma>\<P> \<^bold>\<and> \<^bold>\<not>\<^bold>\<emptyset>\<^sup>\<gamma>\<^bold>\<in>\<^sup>\<gamma>\<P>\<rfloor>" using A1b T1 by auto 
                  have 2: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<gamma>\<P> \<^bold>\<and> \<phi>\<^bold>\<subseteq>\<^sup>\<gamma>\<psi>) \<^bold>\<rightarrow> \<psi>\<^bold>\<in>\<^sup>\<gamma>\<P>\<rfloor>" by (metis A1b G_def T1 T6 symm)
                  have 3: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<gamma>\<P> \<^bold>\<and> \<psi>\<^bold>\<in>\<^sup>\<gamma>\<P>) \<^bold>\<rightarrow> ((\<phi>\<^bold>\<sqinter>\<^sup>\<gamma>\<psi>)\<^bold>\<in>\<^sup>\<gamma>\<P>)\<rfloor>" by (metis A1b G_def T1 T6 symm)
                  have 4: "\<lfloor>\<^bold>\<forall>\<phi>. \<phi>\<^bold>\<in>\<^sup>\<gamma>\<P> \<^bold>\<or> (\<inverse>\<^sup>\<gamma>\<phi>)\<^bold>\<in>\<^sup>\<gamma>\<P>\<rfloor>" using A1b by blast
                  thus ?thesis by (simp add: 1 2 3 4) qed
 (*U3*) theorem U3: "\<lfloor>\<^bold>\<forall>\<phi>. \<phi>\<^bold>\<in>\<^sup>\<gamma>\<P>' \<^bold>\<leftrightarrow> \<phi>\<^bold>\<in>\<^sup>\<gamma>\<P>\<rfloor>" by (metis A1b G_def T1 T6 symm) (*\<P>' and \<P> are equal*)
(**Modal logic S5**)
  axiomatization where refl: "\<forall>x. x r x" and trans: "\<forall>x y z. x r y \<and> y r z \<longrightarrow> x r z"
  lemma True nitpick[satisfy,user_axioms] oops (*Model found by Nitpick*)
(**Barcan and converse Barcan formula for individuals (type e) and properties (type e\<Rightarrow>i\<Rightarrow>bool)**)
  lemma Bind1: "\<lfloor>(\<^bold>\<forall>\<^sup>Ex::e.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex::e. \<phi> x)\<rfloor>" using MC symm by blast
  lemma CBind1: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex::e. \<phi> x) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex::e.\<^bold>\<box>(\<phi> x))\<rfloor>" using MC by blast
  lemma Bpred1: "\<lfloor>(\<^bold>\<forall>x::e\<Rightarrow>i\<Rightarrow>bool. \<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x::e\<Rightarrow>i\<Rightarrow>bool. \<phi> x)\<rfloor>" by simp 
  lemma CBpred1: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x::e\<Rightarrow>i\<Rightarrow>bool. \<phi> x) \<^bold>\<rightarrow> (\<^bold>\<forall>x::e\<Rightarrow>i\<Rightarrow>bool. \<^bold>\<box>(\<phi> x))\<rfloor>" by simp
end