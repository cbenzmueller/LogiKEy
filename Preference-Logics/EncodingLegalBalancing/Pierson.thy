theory Pierson imports GeneralKnowledge (*** Benzmüller, Fuenmayor & Lomfeld, 2021 ***)  
begin (*** Pierson v. Post "wild animal" case **)
 (*unimportant*) nitpick_params[user_axioms,expect=genuine,show_all,format=3]
 (*case-specific 'world-vocabulary'*)
consts \<alpha>::"e" (*appropriated animal (fox in this case) *)
consts Pursue::"c\<Rightarrow>e\<Rightarrow>\<sigma>" Capture::"c\<Rightarrow>e\<Rightarrow>\<sigma>"
(************** pro-defendant (Pierson) argument **************)
 (*defendant's theory*)
abbreviation "dT1 \<equiv> \<lfloor>(\<^bold>\<exists>c. Capture c \<alpha> \<^bold>\<and> \<^bold>\<not>Domestic \<alpha>) \<^bold>\<rightarrow> appWildAnimal\<rfloor>"
abbreviation "dT2 \<equiv> \<lfloor>\<^bold>\<forall>c. Pursue c \<alpha> \<^bold>\<rightarrow> Intent c\<rfloor>"
abbreviation "dT3 \<equiv> \<lfloor>\<^bold>\<forall>c. Capture c \<alpha> \<^bold>\<rightarrow> Poss c\<rfloor>"
abbreviation "d_theory \<equiv> dT1 \<and> dT2 \<and> dT3"
 (*defendant's facts*)
abbreviation "dF1 w \<equiv> Fox \<alpha> w"
abbreviation "dF2 w \<equiv> FreeRoaming \<alpha> w"
abbreviation "dF3 w \<equiv> \<^bold>\<not>Pet \<alpha> w"
abbreviation "dF4 w \<equiv> Pursue p \<alpha> w"
abbreviation "dF5 w \<equiv> Capture d \<alpha> w"
abbreviation "d_facts \<equiv> dF1 \<^bold>\<and> dF2 \<^bold>\<and> dF3 \<^bold>\<and> dF4 \<^bold>\<and> dF5"
 (*decision for defendant (Pierson) can be proven automatically*)
theorem Pierson: "d_theory \<longrightarrow> \<lfloor>d_facts \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<prec>For d\<rfloor>"
  by (smt F1 F3 ForAx R2 W5 W7 other.simps tSBR)
 (*we reconstruct the reasoning process leading to the decision for the defendant*)
theorem Pierson': assumes d_theory and "d_facts w" shows "\<^bold>\<box>\<^sup>\<prec>For d w"
proof -
  have 1: "appWildAnimal w"    using W5 W7 assms by blast
  have 2: "\<lfloor>[WILL\<^sup>p]\<^bold>\<prec>[STAB\<^sup>d]\<rfloor>"  using 1 R2 assms by fastforce
  have 3: "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>[WILL\<^sup>p]) \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>\<prec>[STAB\<^sup>d]\<rfloor>" using 2 tSBR by smt
  have 4: "\<^bold>\<box>\<^sup>\<prec>(For p \<^bold>\<leftrightarrow> \<^bold>\<diamond>\<^sup>\<prec>[WILL\<^sup>p]) w" using F1 assms by meson
  have 5: "\<^bold>\<box>\<^sup>\<prec>(For d \<^bold>\<leftrightarrow> \<^bold>\<diamond>\<^sup>\<prec>[STAB\<^sup>d]) w" using F3 assms by meson
  have 6: "\<^bold>\<box>\<^sup>\<prec>((\<^bold>\<diamond>\<^sup>\<prec>[WILL\<^sup>p]) \<^bold>\<or> (\<^bold>\<diamond>\<^sup>\<prec>[STAB\<^sup>d])) w" using 4 5 ForAx by (smt other.simps)
  have 7: "\<^bold>\<box>\<^sup>\<prec>(\<^bold>\<diamond>\<^sup>\<prec>[STAB\<^sup>d]) w" using 3 6 by blast
  have 8: "\<^bold>\<box>\<^sup>\<prec>(For d) w" using 5 7 by simp
  then show ?thesis by simp           
qed
(************** Further checks (using model finder) ****************)
 (*defendant's theory and facts are logically consistent*)
lemma "d_theory \<and> \<lfloor>d_facts\<rfloor>" nitpick[satisfy,card \<iota>=3] oops (*(non-trivial) model found*)
 (*decision for defendant is compatible with premises and lacks value conflicts*)
lemma "\<lfloor>\<^bold>\<not>Conflict\<^sup>p\<rfloor> \<and> \<lfloor>\<^bold>\<not>Conflict\<^sup>d\<rfloor> \<and> d_theory \<and> \<lfloor>d_facts \<^bold>\<and> For d\<rfloor>"
  nitpick[satisfy,card \<iota>=3] oops (* (non-trivial) model found*)
 (*situations where decision holds for plaintiff are compatible too*)
lemma "\<lfloor>\<^bold>\<not>Conflict\<^sup>p\<rfloor> \<and> \<lfloor>\<^bold>\<not>Conflict\<^sup>d\<rfloor> \<and> d_theory \<and> \<lfloor>d_facts \<^bold>\<and> For p\<rfloor>"
  nitpick[satisfy,card \<iota>=3] oops (* (non-trivial) model found*)
end

