section\<open>Variants: the earlier formalisation, and an optional argumentative bridge\<close>

theory FatioFaithful_variants
  imports FatioFaithful_protocol
begin

text\<open>The reconstruction restores several features that the earlier formalisation
\<^cite>\<open>"PasettoBenzmueller2024"\<close> had simplified away: the sign-sensitive
pre-condition of question, the consistency filter on the state update, and the
post-conditions of question and challenge. Since removing those simplifications
changes the object of study, the earlier treatments are recorded here, so that
the difference is visible and checkable rather than merely asserted.\<close>

subsection\<open>Variant: the original, sign-blind question pre-condition\<close>

text\<open>For comparison, the pre-condition of question exactly as in the sources
accompanying \<^cite>\<open>"PasettoBenzmueller2024"\<close>: it requires a POSITIVE obligation of
the addressed speaker and requests a POSITIVE justification. All other clauses
are unchanged, so the two protocols differ only in this one respect.\<close>

fun PreCondO :: "DOS\<Rightarrow>(BDF\<Rightarrow>bool)\<Rightarrow>FatioL\<Rightarrow>bool" where
    "PreCondO dos \<Gamma> question[j,i,\<phi>] =
       (i\<noteq>j \<and> (Entry i \<phi> \<oplus>) \<in> set dos \<and>
        (\<forall>k. k\<noteq>j \<longrightarrow> \<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (ExJD i \<oplus> \<phi>)))))"
  | "PreCondO dos \<Gamma> l = PreCond dos \<Gamma> l"

fun FatioCheckRecO :: "FatioL list\<Rightarrow>DOS\<Rightarrow>(BDF\<Rightarrow>bool)\<Rightarrow>bool" where
    "FatioCheckRecO [] dos \<Gamma> = True"
  | "FatioCheckRecO (l#ls) dos \<Gamma> =
       (PreCondO dos \<Gamma> l \<and> FatioCheckRecO ls (DOSUpdate l dos) (GammaUpdate l \<Gamma>))"

text\<open>The two agree except on question, and on question they agree whenever the
addressed obligation is positive; they differ exactly when it is negative, i.e.
when the question addresses a speaker who has challenged.\<close>

lemma PreCondO_eq_off_question:
  assumes "\<And>j i \<phi>. l \<noteq> question[j,i,\<phi>]"
  shows "PreCondO dos \<Gamma> l = PreCond dos \<Gamma> l"
  using assms by (cases l) auto

lemma PreCondO_blocks_negative:
  assumes "(Entry i \<phi> \<oplus>) \<notin> set dos"
  shows "\<not> PreCondO dos \<Gamma> question[j,i,\<phi>]"
  using assms by simp

subsection\<open>Variant: the earlier, unfiltered state update\<close>

text\<open>The earlier formalisation updated the state by plain union, with the filter
present but deactivated. That variant is recorded here, together with the reason
the filter is active in the reconstruction: an inconsistent state trivialises
every pre-condition.\<close>

lemma ClashTrivialises:
  assumes "\<Gamma> \<psi>" and "\<Gamma> (\<not>\<^sup>d\<psi>)"
  shows "\<Gamma> \<Turnstile> \<phi>"
proof (unfold ConsD_def, intro allI impI)
  fix W B D V U E w
  assume sat: "\<forall>\<gamma>. \<Gamma> \<gamma> \<longrightarrow> (\<forall>w:W. \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<gamma>)" and wW: "W w"
  have "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<psi>" using sat assms(1) wW by blast
  moreover have "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<not>\<^sup>d\<psi>" using sat assms(2) wW by blast
  ultimately show "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<phi>" by simp
qed

definition GammaUpdateM :: "FatioL\<Rightarrow>(BDF\<Rightarrow>bool)\<Rightarrow>(BDF\<Rightarrow>bool)" where
  "GammaUpdateM l \<Gamma> \<equiv> \<lambda>x. \<Gamma> x \<or> GammaAdd l x \<or> x = Done\<^sup>d l"

lemma GammaUpdate_weaker: "GammaUpdate l \<Gamma> x \<Longrightarrow> GammaUpdateM l \<Gamma> x"
  unfolding GammaUpdate_def GammaUpdateM_def by blast

lemma UpdatesAgree:
  assumes "\<And>x. \<Gamma> x \<Longrightarrow> GammaKeep l x"
  shows "GammaUpdate l \<Gamma> x \<longleftrightarrow> GammaUpdateM l \<Gamma> x"
  using assms unfolding GammaUpdate_def GammaUpdateM_def by blast

lemma UnfilteredKeepsClash:
  fixes i::Speaker and \<phi>::Formula
  assumes "\<Gamma>\<^sub>d = (\<lambda>x. x = \<not>\<^sup>d(Done\<^sup>d assert[i,\<phi>]))"
  shows "GammaUpdateM assert[i,\<phi>] \<Gamma>\<^sub>d (Done\<^sup>d assert[i,\<phi>])
       \<and> GammaUpdateM assert[i,\<phi>] \<Gamma>\<^sub>d (\<not>\<^sup>d(Done\<^sup>d assert[i,\<phi>]))"
  using assms unfolding GammaUpdateM_def by simp

lemma FilteredDropsClash:
  fixes i::Speaker and \<phi>::Formula
  assumes "\<Gamma>\<^sub>d = (\<lambda>x. x = \<not>\<^sup>d(Done\<^sup>d assert[i,\<phi>]))"
  shows "GammaUpdate assert[i,\<phi>] \<Gamma>\<^sub>d (Done\<^sup>d assert[i,\<phi>])
       \<and> \<not> GammaUpdate assert[i,\<phi>] \<Gamma>\<^sub>d (\<not>\<^sup>d(Done\<^sup>d assert[i,\<phi>]))"
  using assms unfolding GammaUpdate_def GammaKeep_def by auto


section\<open>Optional bridge: entailment atoms with content\<close>


text\<open>In both the sources and the reconstruction the entailment atoms are
interpreted by an arbitrary valuation: nothing relates \<open>EntD \<Phi> \<oplus> \<phi>\<close>, read as
"the support is an argument for the claim", to the content logic. Now that the content layer has a
semantics, the natural constraint can be stated: a model is \<open>ArgSound\<close> if every
supported claim is entailed by its support, and every attacked claim is refuted
by it.\<close>

definition CEnt :: "Formula\<Rightarrow>Formula\<Rightarrow>\<V>\<Rightarrow>bool" where
  "CEnt \<Phi> \<phi> V \<equiv> \<forall>w. V,w \<Turnstile>\<^sup>c \<Phi> \<longrightarrow> V,w \<Turnstile>\<^sup>c \<phi>"

definition ArgSound :: "\<V>\<Rightarrow>\<E>\<Rightarrow>bool" where
  "ArgSound V E \<equiv> \<forall>\<Phi> \<phi> w. (E \<Phi> \<oplus> \<phi> w \<longrightarrow> CEnt \<Phi> \<phi> V)
                        \<and> (E \<Phi> \<ominus> \<phi> w \<longrightarrow> CEnt \<Phi> (\<not>\<^sup>c\<phi>) V)"

lemma ArgSound_nontrivial: "ArgSound V (\<lambda>\<Phi> sg \<phi> w. False)"
  unfolding ArgSound_def by simp

lemma ArgSound_canonical: "ArgSound V (\<lambda>\<Phi> sg \<phi> w. case sg of \<oplus> \<Rightarrow> CEnt \<Phi> \<phi> V
                                                        | \<ominus> \<Rightarrow> CEnt \<Phi> (\<not>\<^sup>c\<phi>) V)"
  unfolding ArgSound_def by simp

text\<open>In an \<open>ArgSound\<close> model a justification does what its name suggests: whoever
grants the support must grant the claim. Without the constraint this fails.\<close>

theorem JustificationTransfers:
  assumes sound: "ArgSound V E"
      and just: "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d EntD \<Phi> \<oplus> \<phi>"
      and support: "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d {\<Phi>}\<^sup>d"
    shows "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d {\<phi>}\<^sup>d"
proof -
  have "CEnt \<Phi> \<phi> V" using sound just unfolding ArgSound_def by simp
  moreover have "V,w \<Turnstile>\<^sup>c \<Phi>" using support MapC_faithful by blast
  ultimately have "V,w \<Turnstile>\<^sup>c \<phi>" unfolding CEnt_def by blast
  thus ?thesis using MapC_faithful by blast
qed

theorem WithoutBridgeArbitrary:
  fixes x y::\<S> and V::\<V>
  assumes "V x w" and "\<not> V y w"
  shows "\<langle>W,B,D,V,U,(\<lambda>\<Phi> sg \<phi> w. True)\<rangle>,w \<Turnstile>\<^sup>d EntD (x\<^sup>c) \<oplus> (y\<^sup>c)
       \<and> \<not> CEnt (x\<^sup>c) (y\<^sup>c) V"
  using assms unfolding CEnt_def by auto

text\<open>The bridge is offered, not imposed, and the reason is visible in the running
example: the newspaper review \<open>n\<close> and the quality of the restaurant \<open>r\<close> are
distinct atoms, so \<open>n\<close> does not entail \<open>r\<close> in the content logic. Under \<open>ArgSound\<close>
the justification of the Brigade dialogue would therefore be unavailable - the
support of a real argument is defeasible, not deductive. Keeping the entailment
atoms unconstrained is thus not an oversight of the original formalisation but a
commitment to defeasible support; \<open>ArgSound\<close> records what the deductive reading
would cost.\<close>

theorem DefeasibleSupportNeeded:
  fixes V::\<V> and n r::\<S>
  assumes "V n w" and "\<not> V r w"
  shows "\<not> CEnt (n\<^sup>c) (r\<^sup>c) V"
  using assms unfolding CEnt_def by auto

end
