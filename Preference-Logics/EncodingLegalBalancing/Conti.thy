theory Conti imports GeneralKnowledge       (*** Benzmüller, Fuenmayor & Lomfeld, 2021 ***)  
begin (*** Conti v. ASPCA "wild animal" case **)
 (*unimportant*) nitpick_params[user_axioms,expect=genuine,show_all,format=3]
 (*case-specific 'world-vocabulary'*)
consts \<alpha>::"e" (*appropriated animal (parrot in this case) *)
consts Care::"c\<Rightarrow>e\<Rightarrow>\<sigma>" Prop::"c\<Rightarrow>e\<Rightarrow>\<sigma>" Capture::"c\<Rightarrow>e\<Rightarrow>\<sigma>"
(****************** pro-plaintiff (ASPCA) argument ****************)
 (*plaintiff's theory*)
abbreviation "pT1 \<equiv> \<lfloor>(\<^bold>\<exists>c. Capture c \<alpha> \<^bold>\<and> Domestic \<alpha>) \<^bold>\<rightarrow> appDomAnimal\<rfloor>"
abbreviation "pT2 \<equiv> \<lfloor>\<^bold>\<forall>c. Care c \<alpha> \<^bold>\<rightarrow> Mtn c\<rfloor>"
abbreviation "pT3 \<equiv> \<lfloor>\<^bold>\<forall>c. Prop c \<alpha> \<^bold>\<rightarrow> Own c\<rfloor>"
abbreviation "pT4 \<equiv> \<lfloor>\<^bold>\<forall>c. Capture c \<alpha> \<^bold>\<rightarrow> Poss c\<rfloor>" (*'concedes' to defendant*)
abbreviation "p_theory \<equiv> pT1 \<and> pT2 \<and> pT3 \<and> pT4"
 (*plaintiff's facts*)
abbreviation "pF1 w \<equiv> Parrot \<alpha> w"
abbreviation "pF2 w \<equiv> Pet \<alpha> w"
abbreviation "pF3 w \<equiv> Care p \<alpha> w"
abbreviation "pF4 w \<equiv> Prop p \<alpha> w"
abbreviation "pF5 w \<equiv> Capture d \<alpha> w"
abbreviation "p_facts \<equiv> pF1 \<^bold>\<and> pF2 \<^bold>\<and> pF3 \<^bold>\<and> pF4 \<^bold>\<and> pF5"
 (*decision for plaintiff (ASPCA) can be proven automatically*)
theorem ASPCA: "p_theory \<longrightarrow> \<lfloor>p_facts \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<prec>For p\<rfloor>" 
  by (smt F3 F4 F5 ForAx R3 W6 W8 tBR SBR_def other.simps(1))
 (*we reconstruct the reasoning process leading to the decision for the plaintiff*)
theorem ASPCA': assumes p_theory and "p_facts w" shows "\<^bold>\<box>\<^sup>\<prec>For p w"
proof -
  have 1: "appDomAnimal w" using W6 W8 assms by blast
  have 2: "\<lfloor>[STAB\<^sup>d] \<^bold>\<prec> [RELI\<^sup>p\<^bold>\<oplus>RESP\<^sup>p]\<rfloor>" using 1 R3 by fastforce
  have 3: "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>[STAB\<^sup>d]) \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>\<prec>([RELI\<^sup>p] \<^bold>\<or> [RESP\<^sup>p])\<rfloor>" using 2 tSBR by smt
  have 4: "\<^bold>\<box>\<^sup>\<prec>(For p \<^bold>\<leftrightarrow> \<^bold>\<diamond>\<^sup>\<prec>[RELI\<^sup>p]) w" using F5 assms by metis
  have 5: "\<^bold>\<box>\<^sup>\<prec>(For p \<^bold>\<leftrightarrow> \<^bold>\<diamond>\<^sup>\<prec>[RESP\<^sup>p]) w" using F4 assms by metis
  have 6: "\<^bold>\<box>\<^sup>\<prec>(For d \<^bold>\<leftrightarrow> \<^bold>\<diamond>\<^sup>\<prec>[STAB\<^sup>d]) w" using F3 assms by meson
  have 7: "\<^bold>\<box>\<^sup>\<prec>((\<^bold>\<diamond>\<^sup>\<prec>[RELI\<^sup>p]) \<^bold>\<or> (\<^bold>\<diamond>\<^sup>\<prec>[RESP\<^sup>p]) \<^bold>\<or> (\<^bold>\<diamond>\<^sup>\<prec>[STAB\<^sup>d])) w" 
    using 4 5 6 ForAx by (smt other.simps)
  have 8: "\<^bold>\<box>\<^sup>\<prec>((\<^bold>\<diamond>\<^sup>\<prec>[RELI\<^sup>p]) \<^bold>\<or> (\<^bold>\<diamond>\<^sup>\<prec>[RESP\<^sup>p])) w" using 3 7 by metis
  have 9: "\<^bold>\<box>\<^sup>\<prec>(For p) w" using 4 5 8 by auto
  then show ?thesis by simp           
qed
(************** Further checks (using model finder) ****************)
 (*plaintiff's theory and facts are logically consistent*)
lemma "p_theory \<and> \<lfloor>p_facts\<rfloor>" nitpick[satisfy,card \<iota>=3] oops (*(non-trivial) model found*)
 (*decision for plaintiff is compatible with premises and lacks value conflicts*)
lemma "\<lfloor>\<^bold>\<not>Conflict\<^sup>p\<rfloor> \<and> \<lfloor>\<^bold>\<not>Conflict\<^sup>d\<rfloor> \<and> p_theory \<and> \<lfloor>p_facts \<^bold>\<and> For p\<rfloor>"
  nitpick[satisfy,card \<iota>=3] oops (* (non-trivial) model found*)
 (*situations where decision holds for defendant are compatible too*)
lemma "\<lfloor>\<^bold>\<not>Conflict\<^sup>p\<rfloor> \<and> \<lfloor>\<^bold>\<not>Conflict\<^sup>d\<rfloor> \<and> p_theory \<and> \<lfloor>p_facts \<^bold>\<and> For d\<rfloor>"
  nitpick[satisfy,card \<iota>=3] oops (* (non-trivial) model found*)
end

