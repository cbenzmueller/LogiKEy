theory Post imports GeneralKnowledge     (*** Benzmüller, Fuenmayor & Lomfeld, 2021 ***)  
begin (*** Pierson v. Post "wild animal" case **)
 (*unimportant*) nitpick_params[user_axioms,expect=genuine,show_all,format=3]
 (*case-specific 'world-vocabulary'*)
consts \<alpha>::"e" (*appropriated animal (fox in this case) *)
consts Pursue::"c\<Rightarrow>e\<Rightarrow>\<sigma>" Capture::"c\<Rightarrow>e\<Rightarrow>\<sigma>"
(****************** pro-plaintiff (Post) argument ****************)
 (*acknowledges from defendant's theory*)
abbreviation "dT2 \<equiv> \<lfloor>\<^bold>\<forall>c. Pursue c \<alpha> \<^bold>\<rightarrow> Intent c\<rfloor>"
abbreviation "dT3 \<equiv> \<lfloor>\<^bold>\<forall>c. Capture c \<alpha> \<^bold>\<rightarrow> Poss c\<rfloor>"
 (*theory amendment: the animal was chased by a professional hunter (Post); protecting 
   hunters' labor, thus fostering economic efficiency, prevails over legal certainty.*)
consts Hunter::"c\<Rightarrow>\<sigma>" hunting::"\<sigma>" (*new kind of situation: hunting*)
 (*plaintiff's theory*)
abbreviation "pT1 \<equiv> \<lfloor>(\<^bold>\<exists>c. Hunter c \<^bold>\<and> Pursue c \<alpha>) \<^bold>\<rightarrow> hunting\<rfloor>" 
abbreviation "pT2 \<equiv> \<forall>x. \<lfloor>hunting \<^bold>\<rightarrow> ([STAB\<^sup>x\<inverse>] \<^bold>\<prec> [EFFI\<^sup>x\<^bold>\<oplus>WILL\<^sup>x])\<rfloor>" (*case-specific rule*)
abbreviation "pT3 \<equiv> \<forall>x. Promotes (hunting \<^bold>\<and> Hunter x) (For x) EFFI\<^sup>x"
abbreviation "p_theory \<equiv> pT1 \<and> pT2 \<and> pT3 \<and> dT2 \<and> dT3"
 (*plaintiff's facts*)
abbreviation "pF1 w \<equiv> Fox \<alpha> w"
abbreviation "pF2 w \<equiv> Hunter p w"
abbreviation "pF3 w \<equiv> Pursue p \<alpha> w"
abbreviation "pF4 w \<equiv> Capture d \<alpha> w"
abbreviation "p_facts \<equiv> pF1 \<^bold>\<and> pF2 \<^bold>\<and> pF3 \<^bold>\<and> pF4"
 (*decision for plaintiff (Post) can be proven automatically*)
theorem Post: "p_theory \<longrightarrow> \<lfloor>p_facts \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<prec>For p\<rfloor>" 
  by (smt F1 F3 ForAx tBR SBR_def other.simps)
 (*we reconstruct the reasoning process leading to the decision for the plaintiff*)
theorem Post': assumes p_theory and "p_facts w" shows "\<^bold>\<box>\<^sup>\<prec>For p w"
proof -
  have 1: "hunting w" using assms by auto
  have 2: "\<lfloor>[STAB\<^sup>d] \<^bold>\<prec> [EFFI\<^sup>p\<^bold>\<oplus>WILL\<^sup>p]\<rfloor>"  using 1 assms by auto
  have 3: "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>[STAB\<^sup>d]) \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>\<prec>([EFFI\<^sup>p] \<^bold>\<or> [WILL\<^sup>p])\<rfloor>" using 2 tSBR by smt
  have 4: "\<^bold>\<box>\<^sup>\<prec>(For p \<^bold>\<leftrightarrow> \<^bold>\<diamond>\<^sup>\<prec>[EFFI\<^sup>p]) w" using assms by meson
  have 5: "\<^bold>\<box>\<^sup>\<prec>(For p \<^bold>\<leftrightarrow> \<^bold>\<diamond>\<^sup>\<prec>[WILL\<^sup>p]) w" using F1 assms by meson
  have 6: "\<^bold>\<box>\<^sup>\<prec>(For d \<^bold>\<leftrightarrow> \<^bold>\<diamond>\<^sup>\<prec>[STAB\<^sup>d]) w" using F3 assms by meson
  have 7: "\<^bold>\<box>\<^sup>\<prec>((\<^bold>\<diamond>\<^sup>\<prec>[EFFI\<^sup>p]) \<^bold>\<or> (\<^bold>\<diamond>\<^sup>\<prec>[WILL\<^sup>p]) \<^bold>\<or> (\<^bold>\<diamond>\<^sup>\<prec>[STAB\<^sup>d])) w" 
    using 4 5 6 ForAx by (smt other.simps)
  have 8: "\<^bold>\<box>\<^sup>\<prec>((\<^bold>\<diamond>\<^sup>\<prec>[EFFI\<^sup>p]) \<^bold>\<or> (\<^bold>\<diamond>\<^sup>\<prec>[WILL\<^sup>p])) w" using 3 7 by metis
  have 9: "\<^bold>\<box>\<^sup>\<prec>(For p) w" using 4 5 8 by auto
  then show ?thesis by simp           
qed
(************** Further checks (using model finder) ****************)
 (*plaintiff's theory and facts are logically consistent*)
lemma "p_theory \<and> \<lfloor>p_facts\<rfloor>" nitpick[satisfy,card \<iota>=2] oops (*(non-trivial) model found*)
 (*decision for plaintiff is compatible with premises and lacks value conflicts*)
lemma "\<lfloor>\<^bold>\<not>Conflict\<^sup>p\<rfloor> \<and> \<lfloor>\<^bold>\<not>Conflict\<^sup>d\<rfloor> \<and> p_theory \<and> \<lfloor>p_facts \<^bold>\<and> For p\<rfloor>"
  nitpick[satisfy,card \<iota>=2] oops (* (non-trivial) model found*)
 (*situations where decision holds for defendant are compatible too*)
lemma "\<lfloor>\<^bold>\<not>Conflict\<^sup>p\<rfloor> \<and> \<lfloor>\<^bold>\<not>Conflict\<^sup>d\<rfloor> \<and> p_theory \<and> \<lfloor>p_facts \<^bold>\<and> For d\<rfloor>"
  nitpick[satisfy,card \<iota>=2] oops (* (non-trivial) model found*)
end
