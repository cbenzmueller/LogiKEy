section\<open>Tests: two dialogues, checked with high automation\<close>

theory FatioFaithful_tests
  imports FatioFaithful_variants
begin

\<comment>\<open>example content atoms (as in the Fatio paper)\<close>
consts p::\<S> q::\<S> r::\<S> n::\<S> m::\<S> s::\<S>

subsection\<open>The full Brigade Restaurant dialogue (from the literature)\<close>

text\<open>The six-locution Brigade Restaurant dialogue. It appears in the example file
of the Isabelle sources accompanying \<^cite>\<open>"PasettoBenzmueller2024"\<close>, attributed
there to the original Fatio paper \<^cite>\<open>"McBurneyParsons2005"\<close>: a asserts that the
restaurant is good (r); b challenges; a justifies from the newspaper review (n);
c questions b, whose obligation is \<^emph>\<open>negative\<close>, having arisen from the challenge; b
justifies negatively from the chef change and the quality drop (\<open>m \<and>\<^sup>c s\<close>); finally a
retracts. In the original sources the corresponding lemma is stated with empty
world knowledge and left open (with a counterexample noted); here the initial
knowledge \<open>\<Gamma>\<^sub>B\<close> supplies exactly the mental-state formulas that the pre-conditions
require, and the sign-generalised question pre-condition (see the protocol theory)
makes the fourth locution applicable, so that the dialogue checks.\<close>

definition \<Gamma>\<^sub>B :: "BDF\<Rightarrow>bool" where "\<Gamma>\<^sub>B \<equiv> \<lambda>x.
    (\<exists>j. j\<noteq>a \<and> x = \<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d)))
  \<or> (\<exists>k. k\<noteq>b \<and> x = \<D>\<^sup>d b (\<B>\<^sup>d k (\<not>\<^sup>d(\<B>\<^sup>d b {r\<^sup>c}\<^sup>d))))
  \<or> (\<exists>k. k\<noteq>b \<and> x = \<D>\<^sup>d b (\<B>\<^sup>d k (\<D>\<^sup>d b (ExJD a \<oplus> (r\<^sup>c)))))
  \<or> (\<exists>k. k\<noteq>a \<and> x = \<D>\<^sup>d a (\<B>\<^sup>d k (\<B>\<^sup>d a (EntD (n\<^sup>c) \<oplus> (r\<^sup>c)))))
  \<or> (\<exists>k. k\<noteq>c \<and> x = \<D>\<^sup>d c (\<B>\<^sup>d k (\<D>\<^sup>d c (ExJD b \<ominus> (r\<^sup>c)))))
  \<or> (\<exists>k. k\<noteq>b \<and> x = \<D>\<^sup>d b (\<B>\<^sup>d k (\<B>\<^sup>d b (EntD (m\<^sup>c \<and>\<^sup>c s\<^sup>c) \<ominus> (r\<^sup>c)))))
  \<or> (\<exists>j. j\<noteq>a \<and> x = \<D>\<^sup>d a (\<B>\<^sup>d j (\<not>\<^sup>d(\<B>\<^sup>d a {r\<^sup>c}\<^sup>d))))"

abbreviation "Brigade \<equiv>
  [ assert[a,r\<^sup>c], challenge[b,a,r\<^sup>c], justify[a,n\<^sup>c\<turnstile>\<^sup>\<oplus>r\<^sup>c],
    question[c,b,r\<^sup>c], justify[b,m\<^sup>c \<and>\<^sup>c s\<^sup>c\<turnstile>\<^sup>\<ominus>r\<^sup>c], retract[a,r\<^sup>c,\<oplus>] ]"

text\<open>Automation. Every step obligation is discharged by a single automated call
(\<open>auto\<close> with the two protocol definitions and \<open>MemberEntails\<close> as an introduction
rule; the side conditions created by the state filter are closed by the
\<open>GammaKeep\<close> simplification rules of the protocol theory). The justify steps
additionally exhibit their Done-witness in two lines beforehand, and the question
steps select the sign of the addressed obligation. The dialogues themselves are
then assembled from the step lemmas without search.
This division of labour is deliberate: \<open>sledgehammer\<close> \<^cite>\<open>"Sledgehammer2011"\<close>
finds no proof for these steps even with generous time limits and the relevant
facts supplied, because what they require is the choice of a \<^emph>\<open>witness\<close> over a
finite datatype (which speaker questioned or challenged, which sign the
obligation carries) rather than a derivation; automated provers are strong at
the latter and weak at the former. Supplying the witness explicitly and
automating the rest is therefore not a workaround but the appropriate split.\<close>

abbreviation "dos\<^sub>1 \<equiv> DOSUpdate assert[a,r\<^sup>c] []"
abbreviation "dos\<^sub>2 \<equiv> DOSUpdate challenge[b,a,r\<^sup>c] dos\<^sub>1"
abbreviation "dos\<^sub>3 \<equiv> DOSUpdate justify[a,n\<^sup>c\<turnstile>\<^sup>\<oplus>r\<^sup>c] dos\<^sub>2"
abbreviation "dos\<^sub>4 \<equiv> DOSUpdate question[c,b,r\<^sup>c] dos\<^sub>3"
abbreviation "dos\<^sub>5 \<equiv> DOSUpdate justify[b,m\<^sup>c \<and>\<^sup>c s\<^sup>c\<turnstile>\<^sup>\<ominus>r\<^sup>c] dos\<^sub>4"
abbreviation "\<Gamma>\<^sub>1 \<equiv> GammaUpdate assert[a,r\<^sup>c] \<Gamma>\<^sub>B"
abbreviation "\<Gamma>\<^sub>2 \<equiv> GammaUpdate challenge[b,a,r\<^sup>c] \<Gamma>\<^sub>1"
abbreviation "\<Gamma>\<^sub>3 \<equiv> GammaUpdate justify[a,n\<^sup>c\<turnstile>\<^sup>\<oplus>r\<^sup>c] \<Gamma>\<^sub>2"
abbreviation "\<Gamma>\<^sub>4 \<equiv> GammaUpdate question[c,b,r\<^sup>c] \<Gamma>\<^sub>3"
abbreviation "\<Gamma>\<^sub>5 \<equiv> GammaUpdate justify[b,m\<^sup>c \<and>\<^sup>c s\<^sup>c\<turnstile>\<^sup>\<ominus>r\<^sup>c] \<Gamma>\<^sub>4"

lemma B1: "PreCond [] \<Gamma>\<^sub>B assert[a,r\<^sup>c]"
  by (auto simp: \<Gamma>\<^sub>B_def intro!: MemberEntails)
lemma B2: "PreCond dos\<^sub>1 \<Gamma>\<^sub>1 challenge[b,a,r\<^sup>c]"
  by (auto simp: \<Gamma>\<^sub>B_def GammaUpdate_def intro!: MemberEntails)
lemma B3: "PreCond dos\<^sub>2 \<Gamma>\<^sub>2 justify[a,n\<^sup>c\<turnstile>\<^sup>\<oplus>r\<^sup>c]"
proof -
  have "\<Gamma>\<^sub>2 (Done\<^sup>d challenge[b,a,r\<^sup>c])" by (simp add: GammaUpdate_def)
  hence "\<exists>j. j\<noteq>a \<and> (\<Gamma>\<^sub>2 (Done\<^sup>d question[j,a,r\<^sup>c]) \<or> \<Gamma>\<^sub>2 (Done\<^sup>d challenge[j,a,r\<^sup>c]))"
    by (intro exI[of _ b]) simp
  thus ?thesis by (auto simp: \<Gamma>\<^sub>B_def GammaUpdate_def intro!: MemberEntails)
qed
lemma B4: "PreCond dos\<^sub>3 \<Gamma>\<^sub>3 question[c,b,r\<^sup>c]"
  by (intro PreCond.simps[THEN iffD2] conjI exI[of _ \<ominus>])
     (auto simp: \<Gamma>\<^sub>B_def GammaUpdate_def intro!: MemberEntails)
lemma B5: "PreCond dos\<^sub>4 \<Gamma>\<^sub>4 justify[b,m\<^sup>c \<and>\<^sup>c s\<^sup>c\<turnstile>\<^sup>\<ominus>r\<^sup>c]"
proof -
  have "\<Gamma>\<^sub>4 (Done\<^sup>d question[c,b,r\<^sup>c])" by (simp add: GammaUpdate_def)
  hence "\<exists>j. j\<noteq>b \<and> (\<Gamma>\<^sub>4 (Done\<^sup>d question[j,b,r\<^sup>c]) \<or> \<Gamma>\<^sub>4 (Done\<^sup>d challenge[j,b,r\<^sup>c]))"
    by (intro exI[of _ c]) simp
  thus ?thesis by (auto simp: \<Gamma>\<^sub>B_def GammaUpdate_def intro!: MemberEntails)
qed
lemma B6: "PreCond dos\<^sub>5 \<Gamma>\<^sub>5 retract[a,r\<^sup>c,\<oplus>]"
  by (auto simp: \<Gamma>\<^sub>B_def GammaUpdate_def intro!: MemberEntails)

theorem BrigadeDialogue: "FatioCheckRec Brigade [] \<Gamma>\<^sub>B"
  unfolding FatioCheckRec.simps
  by (intro conjI TrueI) (fact B1, fact B2, fact B3, fact B4, fact B5, fact B6)

subsection\<open>A further example, constructed here: role reversal with a negative retraction\<close>

text\<open>Seven locutions over two topics: after the exchange on p is settled by b
retracting its \<^emph>\<open>negative\<close> obligation (exercising the \<open>\<ominus>\<close>-clause of retract), the
roles reverse and b becomes the asserter of q, questioned by a.\<close>

definition \<Gamma>\<^sub>C :: "BDF\<Rightarrow>bool" where "\<Gamma>\<^sub>C \<equiv> \<lambda>x.
    (\<exists>j. j\<noteq>a \<and> x = \<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {p\<^sup>c}\<^sup>d)))
  \<or> (\<exists>k. k\<noteq>b \<and> x = \<D>\<^sup>d b (\<B>\<^sup>d k (\<not>\<^sup>d(\<B>\<^sup>d b {p\<^sup>c}\<^sup>d))))
  \<or> (\<exists>k. k\<noteq>b \<and> x = \<D>\<^sup>d b (\<B>\<^sup>d k (\<D>\<^sup>d b (ExJD a \<oplus> (p\<^sup>c)))))
  \<or> (\<exists>k. k\<noteq>a \<and> x = \<D>\<^sup>d a (\<B>\<^sup>d k (\<B>\<^sup>d a (EntD (n\<^sup>c) \<oplus> (p\<^sup>c)))))
  \<or> (\<exists>j. j\<noteq>b \<and> x = \<D>\<^sup>d b (\<B>\<^sup>d j (\<not>\<^sup>d\<not>\<^sup>d(\<B>\<^sup>d b {p\<^sup>c}\<^sup>d))))
  \<or> (\<exists>j. j\<noteq>b \<and> x = \<D>\<^sup>d b (\<B>\<^sup>d j (\<B>\<^sup>d b {q\<^sup>c}\<^sup>d)))
  \<or> (\<exists>k. k\<noteq>a \<and> x = \<D>\<^sup>d a (\<B>\<^sup>d k (\<D>\<^sup>d a (ExJD b \<oplus> (q\<^sup>c)))))
  \<or> (\<exists>k. k\<noteq>b \<and> x = \<D>\<^sup>d b (\<B>\<^sup>d k (\<B>\<^sup>d b (EntD (m\<^sup>c) \<oplus> (q\<^sup>c)))))"

abbreviation "Cascade \<equiv>
  [ assert[a,p\<^sup>c], challenge[b,a,p\<^sup>c], justify[a,n\<^sup>c\<turnstile>\<^sup>\<oplus>p\<^sup>c], retract[b,p\<^sup>c,\<ominus>],
    assert[b,q\<^sup>c], question[a,b,q\<^sup>c], justify[b,m\<^sup>c\<turnstile>\<^sup>\<oplus>q\<^sup>c] ]"

abbreviation "cd\<^sub>1 \<equiv> DOSUpdate assert[a,p\<^sup>c] []"
abbreviation "cd\<^sub>2 \<equiv> DOSUpdate challenge[b,a,p\<^sup>c] cd\<^sub>1"
abbreviation "cd\<^sub>3 \<equiv> DOSUpdate justify[a,n\<^sup>c\<turnstile>\<^sup>\<oplus>p\<^sup>c] cd\<^sub>2"
abbreviation "cd\<^sub>4 \<equiv> DOSUpdate retract[b,p\<^sup>c,\<ominus>] cd\<^sub>3"
abbreviation "cd\<^sub>5 \<equiv> DOSUpdate assert[b,q\<^sup>c] cd\<^sub>4"
abbreviation "cd\<^sub>6 \<equiv> DOSUpdate question[a,b,q\<^sup>c] cd\<^sub>5"
abbreviation "\<Delta>\<^sub>1 \<equiv> GammaUpdate assert[a,p\<^sup>c] \<Gamma>\<^sub>C"
abbreviation "\<Delta>\<^sub>2 \<equiv> GammaUpdate challenge[b,a,p\<^sup>c] \<Delta>\<^sub>1"
abbreviation "\<Delta>\<^sub>3 \<equiv> GammaUpdate justify[a,n\<^sup>c\<turnstile>\<^sup>\<oplus>p\<^sup>c] \<Delta>\<^sub>2"
abbreviation "\<Delta>\<^sub>4 \<equiv> GammaUpdate retract[b,p\<^sup>c,\<ominus>] \<Delta>\<^sub>3"
abbreviation "\<Delta>\<^sub>5 \<equiv> GammaUpdate assert[b,q\<^sup>c] \<Delta>\<^sub>4"
abbreviation "\<Delta>\<^sub>6 \<equiv> GammaUpdate question[a,b,q\<^sup>c] \<Delta>\<^sub>5"

lemma C1: "PreCond [] \<Gamma>\<^sub>C assert[a,p\<^sup>c]"
  by (auto simp: \<Gamma>\<^sub>C_def intro!: MemberEntails)
lemma C2: "PreCond cd\<^sub>1 \<Delta>\<^sub>1 challenge[b,a,p\<^sup>c]"
  by (auto simp: \<Gamma>\<^sub>C_def GammaUpdate_def intro!: MemberEntails)
lemma C3: "PreCond cd\<^sub>2 \<Delta>\<^sub>2 justify[a,n\<^sup>c\<turnstile>\<^sup>\<oplus>p\<^sup>c]"
proof -
  have "\<Delta>\<^sub>2 (Done\<^sup>d challenge[b,a,p\<^sup>c])" by (simp add: GammaUpdate_def)
  hence "\<exists>j. j\<noteq>a \<and> (\<Delta>\<^sub>2 (Done\<^sup>d question[j,a,p\<^sup>c]) \<or> \<Delta>\<^sub>2 (Done\<^sup>d challenge[j,a,p\<^sup>c]))"
    by (intro exI[of _ b]) simp
  thus ?thesis by (auto simp: \<Gamma>\<^sub>C_def GammaUpdate_def intro!: MemberEntails)
qed
lemma C4: "PreCond cd\<^sub>3 \<Delta>\<^sub>3 retract[b,p\<^sup>c,\<ominus>]"
  by (auto simp: \<Gamma>\<^sub>C_def GammaUpdate_def intro!: MemberEntails)
lemma C5: "PreCond cd\<^sub>4 \<Delta>\<^sub>4 assert[b,q\<^sup>c]"
  by (auto simp: \<Gamma>\<^sub>C_def GammaUpdate_def intro!: MemberEntails)
lemma C6: "PreCond cd\<^sub>5 \<Delta>\<^sub>5 question[a,b,q\<^sup>c]"
  by (intro PreCond.simps[THEN iffD2] conjI exI[of _ \<oplus>])
     (auto simp: \<Gamma>\<^sub>C_def GammaUpdate_def intro!: MemberEntails)
lemma C7: "PreCond cd\<^sub>6 \<Delta>\<^sub>6 justify[b,m\<^sup>c\<turnstile>\<^sup>\<oplus>q\<^sup>c]"
proof -
  have "\<Delta>\<^sub>6 (Done\<^sup>d question[a,b,q\<^sup>c])" by (simp add: GammaUpdate_def)
  hence "\<exists>j. j\<noteq>b \<and> (\<Delta>\<^sub>6 (Done\<^sup>d question[j,b,q\<^sup>c]) \<or> \<Delta>\<^sub>6 (Done\<^sup>d challenge[j,b,q\<^sup>c]))"
    by (intro exI[of _ a]) simp
  thus ?thesis by (auto simp: \<Gamma>\<^sub>C_def GammaUpdate_def intro!: MemberEntails)
qed

theorem CascadeDialogue: "FatioCheckRec Cascade [] \<Gamma>\<^sub>C"
  unfolding FatioCheckRec.simps
  by (intro conjI TrueI) (fact C1, fact C2, fact C3, fact C4, fact C5, fact C6, fact C7)


subsection\<open>Every request in the dialogues is answered\<close>

text\<open>Fatio obliges the addressee of a question or a challenge to respond. With
\<open>Pending\<close> this is checkable: both dialogues leave no request open, whereas their
prefixes up to the response do.\<close>

theorem BrigadeAnswered: "Answered Brigade" unfolding Answered_def by simp
theorem CascadeAnswered: "Answered Cascade" unfolding Answered_def by simp
theorem BrigadePrefixPending: "\<not> Answered (take 2 Brigade)"
  unfolding Answered_def by simp

subsection\<open>Why the dialogue needs the generalised question pre-condition\<close>

text\<open>Under the original, sign-blind pre-condition the fourth locution of the
dialogue is not applicable: c addresses b, whose obligation stems from the
challenge and is therefore negative, so no positive entry for b exists in the
store. The dialogue is consequently rejected by the original checker while being
accepted by the reconstructed one. This makes the deviation discussed in the
protocol theory a theorem rather than a claim.\<close>

theorem OriginalBlocksFourthMove: "\<not> PreCondO dos\<^sub>3 \<Gamma>\<^sub>3 question[c,b,r\<^sup>c]"
  by simp

theorem OriginalRejectsBrigade: "\<not> FatioCheckRecO Brigade [] \<Gamma>\<^sub>B"
  by simp

subsection\<open>The examples are not vacuous\<close>

text\<open>A consequence relation quantified over models is vacuously total on an
unsatisfiable premise set: if no model validated \<open>\<Gamma>\<^sub>B\<close> globally, every pre-condition
would hold for trivial reasons and the dialogue checks above would say nothing.
The following two theorems exclude this. The first exhibits a model of \<open>\<Gamma>\<^sub>B\<close> (all
accessibilities empty, so every belief and desire holds vacuously); the second
shows that \<open>\<Gamma>\<^sub>B\<close> nevertheless does not entail everything, using the same model with
an empty valuation.\<close>

theorem \<Gamma>\<^sub>B_satisfiable:
  "\<forall>\<gamma>. \<Gamma>\<^sub>B \<gamma> \<longrightarrow> (\<forall>w:(\<lambda>w::\<w>. True).
        \<langle>(\<lambda>w::\<w>. True),(\<lambda>i w v. False),(\<lambda>i w v. False),V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<gamma>)"
  by (auto simp: \<Gamma>\<^sub>B_def)

theorem \<Gamma>\<^sub>B_nonvacuous: "\<not> (\<Gamma>\<^sub>B \<Turnstile> q\<^sup>d)"
proof
  assume "\<Gamma>\<^sub>B \<Turnstile> q\<^sup>d"
  from ConsD_E[OF this \<Gamma>\<^sub>B_satisfiable] show False by simp
qed

subsection\<open>Negative tests: the checker discriminates\<close>

text\<open>A checker that accepted everything would also accept the dialogues above.
These three theorems show that it does not: a justification without a preceding
question or challenge, a retraction without a corresponding obligation, and an
assertion repeated while the obligation is still open are all rejected.\<close>

theorem NoJustifyWithoutRequest: "\<not> PreCond dos\<^sub>1 \<Gamma>\<^sub>1 justify[a,n\<^sup>c\<turnstile>\<^sup>\<oplus>r\<^sup>c]"
  by (auto simp: \<Gamma>\<^sub>B_def GammaUpdate_def)

theorem NoRetractWithoutObligation: "\<not> PreCond [] \<Gamma>\<^sub>B retract[a,r\<^sup>c,\<oplus>]"
  by simp

theorem NoRepeatedAssert: "\<not> PreCond dos\<^sub>1 \<Gamma>\<^sub>1 assert[a,r\<^sup>c]"
  by simp

theorem BadDialogueRejected: "\<not> FatioCheckRec [ assert[a,r\<^sup>c], assert[a,r\<^sup>c] ] [] \<Gamma>\<^sub>B"
  by simp

subsection\<open>A pre-condition that does not follow by membership\<close>

text\<open>In the dialogues above every pre-condition is met because the world knowledge
literally contains the required formula. Here the required desire is instead
\<^emph>\<open>derived\<close>, by the K principle transferred from the shallow embedding (see
\<open>ConsK\<D>\<B>\<close> and \<open>DeepK\<B>\<close>): the agent's knowledge contains an implication and its
antecedent, not the conclusion.\<close>

definition \<Gamma>\<^sub>K :: "BDF\<Rightarrow>bool" where "\<Gamma>\<^sub>K \<equiv> \<lambda>x.
    (\<exists>j. j\<noteq>a \<and> x = \<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d \<supset>\<^sup>d \<B>\<^sup>d a {s\<^sup>c}\<^sup>d)))
  \<or> (\<exists>j. j\<noteq>a \<and> x = \<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d)))"

lemma DerivedDesire:
  assumes ja: "j \<noteq> a"
  shows "\<Gamma>\<^sub>K \<Turnstile> \<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {s\<^sup>c}\<^sup>d))"
proof -
  have imp: "\<Gamma>\<^sub>K \<Turnstile> \<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d \<supset>\<^sup>d \<B>\<^sup>d a {s\<^sup>c}\<^sup>d))"
    using ja by (intro MemberEntails) (auto simp: \<Gamma>\<^sub>K_def)
  have ant: "\<Gamma>\<^sub>K \<Turnstile> \<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d))"
    using ja by (intro MemberEntails) (auto simp: \<Gamma>\<^sub>K_def)
  show ?thesis by (rule ConsK\<D>\<B>[OF imp ant])
qed

theorem AssertByDerivation: "PreCond [] \<Gamma>\<^sub>K assert[a,s\<^sup>c]"
  using DerivedDesire by simp

subsection\<open>The same, established on the shallow side\<close>

text\<open>The maximal shallow embedding put to work: the required desire is derived by
reasoning with the shallow connectives only, and the result is transferred to the
deep consequence relation by \<open>ConsD_via_shallow\<close>. This is what the second backend
is for; by faithfulness the two routes agree.\<close>

lemma DerivedDesireShallow:
  assumes ja: "j \<noteq> a"
  shows "\<Gamma>\<^sub>K \<Turnstile> \<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {s\<^sup>c}\<^sup>d))"
proof (rule ConsD_via_shallow)
  fix W::\<W> and B D::\<R> and V::\<V> and U::\<U> and E::\<E> and w::\<w>
  assume wW: "W w"
  assume satS: "\<forall>\<gamma>. \<Gamma>\<^sub>K \<gamma> \<longrightarrow> (\<forall>v:W. \<langle>W,B,D,V,U,E\<rangle>,v \<Turnstile>\<^sup>s \<lparr>\<gamma>\<rparr>)"
  have m1: "\<Gamma>\<^sub>K (\<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d \<supset>\<^sup>d \<B>\<^sup>d a {s\<^sup>c}\<^sup>d)))"
    using ja by (auto simp: \<Gamma>\<^sub>K_def)
  have m2: "\<Gamma>\<^sub>K (\<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d)))"
    using ja by (auto simp: \<Gamma>\<^sub>K_def)
  have X: "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d \<supset>\<^sup>d \<B>\<^sup>d a {s\<^sup>c}\<^sup>d))\<rparr>"
    using satS[THEN spec, of "\<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d \<supset>\<^sup>d \<B>\<^sup>d a {s\<^sup>c}\<^sup>d))"] m1 wW by blast
  have Y: "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d))\<rparr>"
    using satS[THEN spec, of "\<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {r\<^sup>c}\<^sup>d))"] m2 wW by blast
  show "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<D>\<^sup>d a (\<B>\<^sup>d j (\<B>\<^sup>d a {s\<^sup>c}\<^sup>d))\<rparr>" using X Y by auto
qed

theorem AssertByShallowDerivation: "PreCond [] \<Gamma>\<^sub>K assert[a,s\<^sup>c]"
  using DerivedDesireShallow by simp

theorem \<Gamma>\<^sub>C_satisfiable:
  "\<forall>\<gamma>. \<Gamma>\<^sub>C \<gamma> \<longrightarrow> (\<forall>w:(\<lambda>w::\<w>. True).
      \<langle>(\<lambda>w. True),(\<lambda>x w v. False),(\<lambda>x w v. False),(\<lambda>x w. False),U\<^sub>0,E\<^sub>0\<rangle>,w \<Turnstile>\<^sup>d \<gamma>)"
  unfolding \<Gamma>\<^sub>C_def by auto

end
