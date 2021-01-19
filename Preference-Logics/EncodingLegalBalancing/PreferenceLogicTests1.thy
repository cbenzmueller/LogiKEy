theory PreferenceLogicTests1 imports PreferenceLogicBasics (** Benzmüller & Fuenmayor, 2021 **)  
begin (*** Tests for the SSE of van Benthem et al, JPL 2009, in HOL ***)
 (*Fact 1: definability of the principal operators and verification*)
lemma F1_9:  "\<lfloor>(\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>)\<rfloor>" by blast
lemma F1_10: "\<lfloor>(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>E \<psi>)\<rfloor>" by blast 
lemma F1_11: "\<lfloor>(\<phi> \<^bold>\<prec>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<prec>\<^sub>E\<^sub>E \<psi>)\<rfloor>" by blast
lemma F1_12: "\<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>E \<psi>)\<rfloor>" by blast
 (*Fact 2: definability of remaining pref. operators and verification*)
lemma F2_13: "is_total BR \<longrightarrow> \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A \<psi>)\<rfloor>" using SBR_def by blast
lemma F2_14: "is_total BR \<longrightarrow> \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>E\<^sub>A \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<prec>\<^sub>E\<^sub>A \<psi>)\<rfloor>" using SBR_def by blast
lemma F2_15: "is_total BR \<longrightarrow> \<lfloor>(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A \<psi>)\<rfloor>" using SBR_def by blast
lemma F2_16: "is_total BR \<longrightarrow> \<lfloor>(\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>A \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<preceq>\<^sub>E\<^sub>A \<psi>)\<rfloor>" using SBR_def by blast
 (*Section 3.5 "Axiomatization" -- verify interaction axioms*)
lemma Incl_1:   "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<preceq>\<phi>)\<rfloor>"      using SBR_def by blast
lemma Inter_1:  "\<lfloor>(\<^bold>\<diamond>\<^sup>\<preceq>\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<prec>\<phi>)\<rfloor>"   using tBR SBR_def by metis
lemma Trans_le: "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<prec>\<phi>)\<rfloor>"   using tSBR by blast 
lemma Inter_2:  "\<lfloor>(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>) \<^bold>\<rightarrow>  ((\<^bold>\<diamond>\<^sup>\<prec>\<psi>) \<^bold>\<or> \<^bold>\<diamond>\<^sup>\<preceq>(\<psi> \<^bold>\<and>  \<^bold>\<diamond>\<^sup>\<preceq>\<phi>))\<rfloor>" using SBR_def by blast
lemma F4: "\<lfloor>(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<diamond>\<^sup>\<prec>\<psi>) \<^bold>\<or> \<^bold>\<diamond>\<^sup>\<preceq>(\<psi> \<^bold>\<and>  \<^bold>\<diamond>\<^sup>\<preceq>\<phi>))\<rfloor> \<longleftrightarrow> 
            (\<forall>w. \<forall>v. (((w \<preceq> v) \<and> \<not>(v \<preceq> w)) \<longrightarrow> (w \<prec> v)))" using SBR_def by blast
lemma Inter_3: "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<^bold>\<diamond>\<^sup>\<preceq>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<prec>\<phi>)\<rfloor>" using tBR SBR_def by blast
lemma Incl_2:  "\<lfloor>(\<^bold>\<diamond>\<^sup>\<preceq>\<phi>) \<^bold>\<rightarrow> (\<^bold>E\<phi>)\<rfloor>"     by blast
 (*Section 3.6 "A binary preference fragment"*)
 (* \<^bold>\<preceq>\<^sub>E\<^sub>E is the dual of \<^bold>\<prec>\<^sub>A\<^sub>A *)
lemma "\<lfloor>(\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<^bold>\<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor> \<and> \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" by blast
(* \<preceq>\<^sub>E\<^sub>E is the dual of \<prec>\<^sub>A\<^sub>A only if totality is assumed*)
lemma "\<lfloor>(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor>" nitpick oops (*countermodel*)
lemma "\<lfloor>(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<rightarrow> \<^bold>\<not>(\<psi> \<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor>" using SBR_def by blast (*this direction holds*)
lemma "is_total BR \<longrightarrow> \<lfloor>(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor>"  using SBR_def by blast
lemma "\<lfloor>(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" nitpick oops (*countermodel*)
lemma "\<lfloor>(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<rightarrow> \<^bold>\<not>(\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" using SBR_def by blast (*this direction holds*)
lemma "is_total BR \<longrightarrow> \<lfloor>(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" using SBR_def by blast
 (* verify p.97-98 *)
lemma monotonicity: "\<lfloor>((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<and> \<^bold>A(\<phi>\<^bold>\<rightarrow>\<xi>)) \<^bold>\<rightarrow> (\<xi> \<preceq>\<^sub>E\<^sub>E \<psi>)\<rfloor>" by blast
lemma reducibility: "\<lfloor>(((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<and> \<alpha>) \<preceq>\<^sub>E\<^sub>E \<beta>) \<^bold>\<leftrightarrow> ((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>)\<^bold>\<and>(\<alpha> \<preceq>\<^sub>E\<^sub>E \<beta>))\<rfloor>" by blast
lemma reflexivity:   "\<lfloor>\<phi> \<^bold>\<rightarrow> (\<phi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" using rBR by blast
 (*The condition below enforcing totality of the preference relation is supposed to hold.
  However there are countermodels (both local & global consequence). Error in paper?*)
lemma "\<lfloor>((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>) \<^bold>\<and> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<or> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>))\<rfloor>" 
  nitpick oops (*countermodel*)
lemma "\<lfloor>((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>) \<^bold>\<and> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>))\<rfloor> \<longrightarrow> \<lfloor>((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<or> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>))\<rfloor>"
  nitpick oops (*countermodel*)
end

