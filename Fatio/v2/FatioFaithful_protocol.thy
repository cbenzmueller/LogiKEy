section\<open>The Fatio protocol over the deep syntax\<close>

theory FatioFaithful_protocol
  imports FatioFaithful_faithfulness
begin

subsection\<open>Dialectical obligation stores\<close>

datatype DOSEntry = Entry Speaker Formula Sign
type_synonym DOS = "DOSEntry list"

fun DOSUpdate :: "FatioL\<Rightarrow>DOS\<Rightarrow>DOS" where
    "DOSUpdate assert[i,\<phi>] dos = (Entry i \<phi> \<oplus>) # dos"
  | "DOSUpdate question[j,i,\<phi>] dos = dos"
  | "DOSUpdate challenge[j,i,\<phi>] dos = (Entry j \<phi> \<ominus>) # dos"
  | "DOSUpdate (Justify i \<Phi> sg \<phi>) dos = (Entry i \<Phi> sg) # dos"
  | "DOSUpdate retract[i,\<phi>,sg] dos = removeAll (Entry i \<phi> sg) dos"

subsection\<open>Pre-conditions (axiomatic semantics)\<close>

text\<open>Two reconstruction decisions, both recorded explicitly. (1) Following the
Isabelle sources accompanying \<^cite>\<open>"PasettoBenzmueller2024"\<close>, the justify locution
is sign-parametric: \<open>justify[i,\<Phi>\<turnstile>\<^sup>\<ominus>\<phi>]\<close> discharges a negative obligation, as incurred
by a challenge. (2) The pre-condition of question is generalised so that the
requested justification matches the \<^emph>\<open>sign\<close> of the addressed speaker's obligation.
In the original formulation, question requires a \<^emph>\<open>positive\<close> obligation and requests
a positive justification, which makes it inapplicable to a speaker whose
obligation arises from a challenge; the corresponding six-locution dialogue in the
example file of those sources is left open there. The generalisation adopted here
makes that dialogue checkable (see the tests theory).\<close>

fun PreCond :: "DOS\<Rightarrow>(BDF\<Rightarrow>bool)\<Rightarrow>FatioL\<Rightarrow>bool" where
    "PreCond dos \<Gamma> assert[i,\<phi>] =
       ((Entry i \<phi> \<oplus>) \<notin> set dos \<and> (\<forall>j. j\<noteq>i \<longrightarrow> \<Gamma> \<Turnstile> \<D>\<^sup>d i (\<B>\<^sup>d j (\<B>\<^sup>d i {\<phi>}\<^sup>d))))"
  | "PreCond dos \<Gamma> question[j,i,\<phi>] =
       (i\<noteq>j \<and> (\<exists>sg. (Entry i \<phi> sg) \<in> set dos \<and>
        (\<forall>k. k\<noteq>j \<longrightarrow> \<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (ExJD i sg \<phi>))))))"
  | "PreCond dos \<Gamma> challenge[j,i,\<phi>] =
       (i\<noteq>j \<and> (Entry i \<phi> \<oplus>) \<in> set dos \<and>
        (\<forall>k. k\<noteq>j \<longrightarrow> \<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<not>\<^sup>d(\<B>\<^sup>d j {\<phi>}\<^sup>d)))) \<and>
        (\<forall>k. k\<noteq>j \<longrightarrow> \<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (ExJD i \<oplus> \<phi>)))))"
  | "PreCond dos \<Gamma> (Justify i \<Phi> sg \<phi>) =
       ((Entry i \<phi> sg) \<in> set dos \<and>
        (\<exists>j. j\<noteq>i \<and> (\<Gamma> (Done\<^sup>d question[j,i,\<phi>]) \<or> \<Gamma> (Done\<^sup>d challenge[j,i,\<phi>]))) \<and>
        (\<forall>k. k\<noteq>i \<longrightarrow> \<Gamma> \<Turnstile> \<D>\<^sup>d i (\<B>\<^sup>d k (\<B>\<^sup>d i (EntD \<Phi> sg \<phi>)))))"
  | "PreCond dos \<Gamma> retract[i,\<phi>,sg] =
       ((Entry i \<phi> sg) \<in> set dos \<and>
        (case sg of \<oplus> \<Rightarrow> (\<forall>j. j\<noteq>i \<longrightarrow> \<Gamma> \<Turnstile> \<D>\<^sup>d i (\<B>\<^sup>d j (\<not>\<^sup>d(\<B>\<^sup>d i {\<phi>}\<^sup>d))))
                  | \<ominus> \<Rightarrow> (\<forall>j. j\<noteq>i \<longrightarrow> \<Gamma> \<Turnstile> \<D>\<^sup>d i (\<B>\<^sup>d j (\<not>\<^sup>d\<not>\<^sup>d(\<B>\<^sup>d i {\<phi>}\<^sup>d))))))"

subsection\<open>Post-conditions and state evolution\<close>

fun GammaAdd :: "FatioL\<Rightarrow>(BDF\<Rightarrow>bool)" where
    "GammaAdd assert[i,\<phi>] =
       (\<lambda>x. \<exists>k j. k\<noteq>i \<and> j\<noteq>i \<and> x = \<B>\<^sup>d k (\<D>\<^sup>d i (\<B>\<^sup>d j (\<B>\<^sup>d i {\<phi>}\<^sup>d))))"
  | "GammaAdd question[j,i,\<phi>] =
       (\<lambda>x. \<exists>k sg. k\<noteq>j \<and> x = \<B>\<^sup>d k (\<D>\<^sup>d j (ExJD i sg \<phi>)))"
  | "GammaAdd challenge[j,i,\<phi>] =
       (\<lambda>x. \<exists>k. k\<noteq>j \<and> (x = \<B>\<^sup>d k (\<D>\<^sup>d j (ExJD i \<oplus> \<phi>))
                          \<or> x = \<B>\<^sup>d k (\<D>\<^sup>d j (\<not>\<^sup>d(\<B>\<^sup>d j {\<phi>}\<^sup>d)))))"
  | "GammaAdd (Justify i \<Phi> sg \<phi>) =
       (\<lambda>x. \<exists>k j. k\<noteq>i \<and> j\<noteq>i \<and> x = \<B>\<^sup>d k (\<D>\<^sup>d i (\<B>\<^sup>d j (\<B>\<^sup>d i (EntD \<Phi> sg \<phi>)))))"
  | "GammaAdd retract[i,\<phi>,sg] =
       (case sg of \<oplus> \<Rightarrow> (\<lambda>x. \<exists>k j. k\<noteq>i \<and> j\<noteq>i \<and> x = \<B>\<^sup>d k (\<D>\<^sup>d i (\<B>\<^sup>d j (\<not>\<^sup>d(\<B>\<^sup>d i {\<phi>}\<^sup>d)))))
                  | \<ominus> \<Rightarrow> (\<lambda>x. \<exists>k j. k\<noteq>i \<and> j\<noteq>i \<and> x = \<B>\<^sup>d k (\<D>\<^sup>d i (\<B>\<^sup>d j (\<not>\<^sup>d\<not>\<^sup>d(\<B>\<^sup>d i {\<phi>}\<^sup>d))))))"

text\<open>The state update filters: a previously held formula survives unless the
locution asserts its negation. The earlier implementation contained such a filter
but left it deactivated, updating by plain union; that variant, and a theorem
exhibiting a state on which the two differ, are recorded in the variants theory.
Filtering matters because an inconsistent state trivialises every pre-condition
(see \<open>ClashTrivialises\<close> there); independently of it, the satisfiability of the
world knowledge used in the tests theory is verified there.\<close>

\<comment>\<open>Keep an old formula unless it is the negation of what the locution asserts.
   The earlier formalisation contained this filter but left it deactivated; since
   an inconsistent state trivialises every pre-condition (see ClashTrivialises
   below), it is active here, and the unfiltered update is kept as a variant.\<close>
definition GammaKeep :: "FatioL\<Rightarrow>(BDF\<Rightarrow>bool)" where
  "GammaKeep l \<equiv> \<lambda>x. \<not>(\<exists>y. (GammaAdd l y \<or> y = Done\<^sup>d l) \<and> x = \<not>\<^sup>dy)"

\<comment>\<open>A formula can only be filtered out if it is a negation; all other shapes
   survive every update, which discharges the side conditions automatically.\<close>
lemma GammaKeep_AtmD[simp]: "GammaKeep l (x\<^sup>d)" unfolding GammaKeep_def by simp
lemma GammaKeep_DoneD[simp]: "GammaKeep l (Done\<^sup>d l')" unfolding GammaKeep_def by simp
lemma GammaKeep_EntD[simp]: "GammaKeep l (EntD \<Phi> sg \<phi>)" unfolding GammaKeep_def by simp
lemma GammaKeep_ExJD[simp]: "GammaKeep l (ExJD i sg \<phi>)" unfolding GammaKeep_def by simp
lemma GammaKeep_ImpD[simp]: "GammaKeep l (\<phi> \<supset>\<^sup>d \<psi>)" unfolding GammaKeep_def by simp
lemma GammaKeep_BelD[simp]: "GammaKeep l (\<B>\<^sup>d i \<phi>)" unfolding GammaKeep_def by simp
lemma GammaKeep_DesD[simp]: "GammaKeep l (\<D>\<^sup>d i \<phi>)" unfolding GammaKeep_def by simp

definition GammaUpdate :: "FatioL\<Rightarrow>(BDF\<Rightarrow>bool)\<Rightarrow>(BDF\<Rightarrow>bool)" where
  "GammaUpdate l \<Gamma> \<equiv> \<lambda>x. (\<Gamma> x \<and> GammaKeep l x) \<or> GammaAdd l x \<or> x = Done\<^sup>d l"

\<comment>\<open>Checking a dialogue: each locution must meet its pre-condition in the state
   reached so far, and updates store and world knowledge for the rest.\<close>
fun FatioCheckRec :: "FatioL list\<Rightarrow>DOS\<Rightarrow>(BDF\<Rightarrow>bool)\<Rightarrow>bool" where
    "FatioCheckRec [] dos \<Gamma> = True"
  | "FatioCheckRec (l#ls) dos \<Gamma> =
       (PreCond dos \<Gamma> l \<and> FatioCheckRec ls (DOSUpdate l dos) (GammaUpdate l \<Gamma>))"

subsection\<open>Outstanding requests (Fatio's obligation to respond)\<close>

text\<open>A question or a challenge obliges the addressee to respond, by justifying or
by retracting. The earlier formalisation left this to informal combination rules;
here it is made checkable: \<open>Pending\<close> collects the requests that are still open
after a sequence of locutions, and a dialogue is \<open>Answered\<close> when none remain.\<close>

fun Pending :: "FatioL list\<Rightarrow>(Speaker \<times> Formula) set\<Rightarrow>(Speaker \<times> Formula) set" where
    "Pending [] P = P"
  | "Pending (assert[i,\<phi>] # ls) P = Pending ls P"
  | "Pending (question[j,i,\<phi>] # ls) P = Pending ls (insert (i,\<phi>) P)"
  | "Pending (challenge[j,i,\<phi>] # ls) P = Pending ls (insert (i,\<phi>) P)"
  | "Pending (Justify i \<Phi> sg \<phi> # ls) P = Pending ls (P - {(i,\<phi>)})"
  | "Pending (retract[i,\<phi>,sg] # ls) P = Pending ls (P - {(i,\<phi>)})"

definition Answered :: "FatioL list\<Rightarrow>bool" where "Answered ls \<equiv> Pending ls {} = {}"

lemma PendingRequest: "Pending [question[j,i,\<phi>]] {} = {(i,\<phi>)}" by simp
lemma JustifyAnswers: "Answered [question[j,i,\<phi>], Justify i \<Phi> sg \<phi>]"
  unfolding Answered_def by simp
lemma RetractAnswers: "Answered [challenge[j,i,\<phi>], retract[i,\<phi>,sg]]"
  unfolding Answered_def by simp
lemma UnansweredChallenge: "\<not> Answered [assert[i,\<phi>], challenge[j,i,\<phi>]]"
  unfolding Answered_def by simp

subsection\<open>Sanity theorems\<close>

\<comment>\<open>K for the consequence relation, obtained from the shallow side (see the
   faithfulness theory); used for pre-conditions that do not follow by membership\<close>
lemma ConsK\<D>\<B>:
  assumes "\<Gamma> \<Turnstile> \<D>\<^sup>d i (\<B>\<^sup>d j (\<phi> \<supset>\<^sup>d \<psi>))" and "\<Gamma> \<Turnstile> \<D>\<^sup>d i (\<B>\<^sup>d j \<phi>)"
  shows "\<Gamma> \<Turnstile> \<D>\<^sup>d i (\<B>\<^sup>d j \<psi>)"
  using assms unfolding ConsD_def by simp

lemma MemberEntails[intro]: "\<Gamma> \<phi> \<Longrightarrow> \<Gamma> \<Turnstile> \<phi>" unfolding ConsD_def by blast
\<comment>\<open>Consequence is more than membership: the modal K principle for the desire and
belief operators lets a pre-condition follow from world knowledge that does not
contain it literally. This is used in the tests theory.\<close>
lemma ConsK:
  assumes X: "\<Gamma> (\<D>\<^sup>d i (\<B>\<^sup>d j X))" and XY: "\<Gamma> (\<D>\<^sup>d i (\<B>\<^sup>d j (X \<supset>\<^sup>d Y)))"
  shows "\<Gamma> \<Turnstile> \<D>\<^sup>d i (\<B>\<^sup>d j Y)"
proof (rule ConsD_I)
  fix W B D V U E w
  assume sat: "\<forall>\<gamma>. \<Gamma> \<gamma> \<longrightarrow> (\<forall>v:W. \<langle>W,B,D,V,U,E\<rangle>,v \<Turnstile>\<^sup>d \<gamma>)" and wW: "W w"
  have h1: "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<D>\<^sup>d i (\<B>\<^sup>d j X)" using sat X wW by blast
  have h2: "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<D>\<^sup>d i (\<B>\<^sup>d j (X \<supset>\<^sup>d Y))" using sat XY wW by blast
  show "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<D>\<^sup>d i (\<B>\<^sup>d j Y)" using h1 h2 by auto
qed

\<comment>\<open>With the filter active, monotonicity is conditional: a formula survives an
   update unless the locution asserts its negation.\<close>
lemma GammaMono: "\<lbrakk>\<Gamma> x; GammaKeep l x\<rbrakk> \<Longrightarrow> GammaUpdate l \<Gamma> x"
  by (simp add: GammaUpdate_def)
lemma DoneRecorded: "GammaUpdate l \<Gamma> (Done\<^sup>d l)" by (simp add: GammaUpdate_def)
lemma AssertCreatesObligation: "(Entry i \<phi> \<oplus>) \<in> set (DOSUpdate assert[i,\<phi>] dos)" by simp
lemma RetractRemovesObligation: "(Entry i \<phi> sg) \<notin> set (DOSUpdate retract[i,\<phi>,sg] dos)" by simp

end
