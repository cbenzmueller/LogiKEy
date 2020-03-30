theory FittingVariant imports IHOML ModalUltrafilter
begin
(**Positiveness**) consts Positiveness::"\<delta>\<Rightarrow>\<sigma>" ("\<P>")
(**Part I**)
 (*D1*) abbreviation God::\<gamma> ("G") where "G x \<equiv> \<^bold>\<forall>Y::\<delta>. \<P> Y \<^bold>\<rightarrow> \<lparr>Y x\<rparr>"
 (*A1*) axiomatization where A1a:"\<lfloor>\<^bold>\<forall>X. \<P>(\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X)\<rfloor>" and A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<rightharpoondown>X)\<rfloor>" 
 (*A2*) axiomatization where A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. \<lparr>X z\<rparr>\<^bold>\<rightarrow>\<lparr>Y z\<rparr>))) \<^bold>\<rightarrow> \<P> Y\<rfloor>" 
 (*T1*) theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. \<lparr>X z\<rparr>)\<rfloor>" using A1a A2 by blast  
 (*T2*) axiomatization where T2: "\<lfloor>\<P>\<down>G\<rfloor>"     
 (*T3*) theorem T3deRe: "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using T1 T2 by simp
        theorem T3deDicto: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" nitpick[user_axioms] oops (*Countermodel*)
(**Part II*)
 (*Logic KB*)  axiomatization where symm: "\<forall>x y. x r y \<longrightarrow> y r x"
 (*A4*) axiomatization where A4: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>" 
 (*D2*) abbreviation ess::"\<delta>\<Rightarrow>\<gamma>" ("\<E>") where "\<E> Y x \<equiv> \<lparr>Y x\<rparr> \<^bold>\<and> (\<^bold>\<forall>Z.\<lparr>Z x\<rparr>\<^bold>\<rightarrow>(\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. \<lparr>Y z\<rparr>\<^bold>\<rightarrow>\<lparr>Z z\<rparr>)))"
 (*T4*) theorem T4: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> ((\<E>\<down>\<^sub>1G) x)\<rfloor>" using A1b by metis
 (*D3*) definition NE::\<gamma> ("NE") where "NE x  \<equiv> \<^bold>\<forall>Y.  \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. \<lparr>Y z\<rparr>)"
 (*A5*) axiomatization where A5: "\<lfloor>\<P>\<down>NE\<rfloor>" 
    lemma help1: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>"  sorry (*...longer interactive proof, omitted here...*) 
    lemma help2: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X)\<^bold>\<down>G)\<rfloor>" by (metis A4 help1)
 (*T5*) theorem T5deDicto:"\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>\<longrightarrow>\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using T3deRe help1 by blast
        theorem T5deRe:"\<lfloor>(\<lambda>X.\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X)\<^bold>\<down>G\<rfloor> \<longrightarrow> \<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X)\<^bold>\<down>G\<rfloor>" by (metis help2)
 (*T6*) theorem T6deDicto: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using T3deRe help1 by blast
        theorem T6deRe: "\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X)\<^bold>\<down>G\<rfloor>" using T3deRe help2 by blast
(**Modal collapse**) lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[user_axioms] oops (*Countermodel*)
(**Consistency**) lemma True nitpick[satisfy,user_axioms] oops  (*Model found by Nitpick*)
(**Analysis of positive properties using ultrafilters**)
 (*U1*) theorem U1: "\<lfloor>\<delta>-Ultrafilter \<P>\<rfloor>"  (*Sledgehammer succeeds, reconstruction fails*)
          proof - have 1: "\<lfloor>\<^bold>U\<^sup>\<delta>\<^bold>\<in>\<^sup>\<delta>\<P> \<^bold>\<and> \<^bold>\<not>\<^bold>\<emptyset>\<^sup>\<delta>\<^bold>\<in>\<^sup>\<delta>\<P>\<rfloor>" using A1b T1 by auto
                  have 2: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<delta>\<P> \<^bold>\<and> \<phi>\<^bold>\<subseteq>\<^sup>\<delta>\<psi>) \<^bold>\<rightarrow> \<psi>\<^bold>\<in>\<^sup>\<delta>\<P>\<rfloor>" by (metis A1b T3deRe)
                  have 3: "\<lfloor>\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<delta>\<P> \<^bold>\<and> \<psi>\<^bold>\<in>\<^sup>\<delta>\<P>) \<^bold>\<rightarrow> ((\<phi>\<^bold>\<sqinter>\<^sup>\<delta>\<psi>)\<^bold>\<in>\<^sup>\<delta>\<P>)\<rfloor>" by (metis A1b T3deRe)
                  have 4: "\<lfloor>\<^bold>\<forall>\<phi>. \<phi>\<^bold>\<in>\<^sup>\<delta>\<P> \<^bold>\<or> (\<inverse>\<^sup>\<delta>\<phi>)\<^bold>\<in>\<^sup>\<delta>\<P>\<rfloor>" using A1b by blast
                  thus ?thesis by (simp add: 1 2 3 4) qed
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