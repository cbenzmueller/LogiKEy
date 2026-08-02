section\<open>Faithfulness\<close>

theory FatioFaithful_faithfulness
  imports FatioFaithful_shallow FatioFaithful_shallow_minimal
begin

subsection\<open>Faithfulness of the content layer\<close>

primrec DpToShC :: "Formula\<Rightarrow>\<sigma>\<^sub>c" ("\<langle>_\<rangle>\<^sup>c") where
    "\<langle>x\<^sup>c\<rangle>\<^sup>c = x\<^sup>c\<^sup>s" | "\<langle>\<not>\<^sup>c\<phi>\<rangle>\<^sup>c = \<not>\<^sup>c\<^sup>s\<langle>\<phi>\<rangle>\<^sup>c" | "\<langle>\<phi> \<supset>\<^sup>c \<psi>\<rangle>\<^sup>c = \<langle>\<phi>\<rangle>\<^sup>c \<supset>\<^sup>c\<^sup>s \<langle>\<psi>\<rangle>\<^sup>c"

theorem Faithful0a: "\<forall>V w. V,w \<Turnstile>\<^sup>c \<phi> \<longleftrightarrow> \<langle>\<phi>\<rangle>\<^sup>c V w"
  apply (induct \<phi>) by auto

theorem Faithful0b: "\<Turnstile>\<^sup>c \<phi> \<longleftrightarrow> \<Turnstile>\<^sup>c\<^sup>s \<langle>\<phi>\<rangle>\<^sup>c"
  using Faithful0a unfolding ValC_def ValCS_def by auto

\<comment>\<open>Mapping: deep to (maximal) shallow\<close>
primrec DpToSh :: "BDF\<Rightarrow>\<sigma>" ("\<lparr>_\<rparr>") where
    "\<lparr>x\<^sup>a\<rparr> = x\<^sup>s" | "\<lparr>Done\<^sup>d l\<rparr> = Done\<^sup>s l" | "\<lparr>EntD \<Phi> sg \<phi>\<rparr> = EntS \<Phi> sg \<phi>"
  | "\<lparr>ExJD i sg \<phi>\<rparr> = ExJS i sg \<phi>" | "\<lparr>\<not>\<^sup>d\<phi>\<rparr> = \<not>\<^sup>s\<lparr>\<phi>\<rparr>" | "\<lparr>\<phi> \<supset>\<^sup>d \<psi>\<rparr> = \<lparr>\<phi>\<rparr> \<supset>\<^sup>s \<lparr>\<psi>\<rparr>"
  | "\<lparr>\<B>\<^sup>d i \<phi>\<rparr> = \<B>\<^sup>s i \<lparr>\<phi>\<rparr>" | "\<lparr>\<D>\<^sup>d i \<phi>\<rparr> = \<D>\<^sup>s i \<lparr>\<phi>\<rparr>"

\<comment>\<open>Automated faithfulness proofs, as in \<^cite>\<open>"Benzmueller2025Faithful" and "FaithfulPMLinHOL-AFP"\<close>\<close>
theorem Faithful1a:
  "\<forall>W B D V U E. \<forall>w:W. \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<longleftrightarrow> \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr>"
  apply (induct \<phi>) by auto

theorem Faithful1b: "\<Turnstile>\<^sup>d \<phi> \<longleftrightarrow> \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr>"
  using Faithful1a unfolding ValD_def ValS_def by auto

subsection\<open>The content layer: faithfulness of its injection into the BD logic\<close>

text\<open>Besides its own deep and shallow embeddings above, the content layer is
injected into the BD language by \<open>MapC\<close>, and that injection is truth-preserving.
Hence the content layer additionally inherits both shallow embeddings of the BD
logic through \<open>MapC\<close>, and its own validity notion coincides with BD validity of
its image.\<close>

theorem MapC_faithful:
  "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d {\<phi>}\<^sup>d \<longleftrightarrow> V,w \<Turnstile>\<^sup>c \<phi>"
  by (induct \<phi>) auto

theorem MapC_faithful_shallow:
  assumes "W w"
  shows "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>s \<lparr>{\<phi>}\<^sup>d\<rparr> \<longleftrightarrow> V,w \<Turnstile>\<^sup>c \<phi>"
  using assms MapC_faithful[of W B D V U E w \<phi>] Faithful1a[of "{\<phi>}\<^sup>d"] by auto

theorem MapC_validity: "(\<Turnstile>\<^sup>c \<phi>) \<longleftrightarrow> (\<Turnstile>\<^sup>d {\<phi>}\<^sup>d)"
  using MapC_faithful unfolding ValC_def ValD_def by auto

subsection\<open>Discrimination vs. identification: the Done-problem, resolved\<close>

text\<open>Syntactically, \<open>p \<supset>\<^sup>c p\<close> and \<open>\<not>\<^sup>c\<bottom>\<^sup>c\<close> are different contents; hence locutions and
Done-atoms over them are different objects. Semantically, their injections into the
BD logic are equivalent. All four facts are theorems of the reconstruction.\<close>

lemma ContentDiscriminated: "(p\<^sup>c \<supset>\<^sup>c p\<^sup>c) \<noteq> \<not>\<^sup>c\<bottom>\<^sup>c" by simp
lemma LocutionDiscriminated: "assert[a, p\<^sup>c \<supset>\<^sup>c p\<^sup>c] \<noteq> assert[a, \<not>\<^sup>c\<bottom>\<^sup>c]" by simp
lemma DoneDiscriminated: "Done\<^sup>d assert[a, p\<^sup>c \<supset>\<^sup>c p\<^sup>c] \<noteq> Done\<^sup>d assert[a, \<not>\<^sup>c\<bottom>\<^sup>c]" by simp
lemma SemanticsIdentifies:
  "\<Turnstile>\<^sup>d ({p\<^sup>c \<supset>\<^sup>c p\<^sup>c}\<^sup>d \<supset>\<^sup>d {\<not>\<^sup>c\<bottom>\<^sup>c}\<^sup>d) \<and> \<Turnstile>\<^sup>d ({\<not>\<^sup>c\<bottom>\<^sup>c}\<^sup>d \<supset>\<^sup>d {p\<^sup>c \<supset>\<^sup>c p\<^sup>c}\<^sup>d)"
  unfolding ValD_def by simp

subsection\<open>Working on the shallow side: the transfer principle\<close>

text\<open>The maximal shallow embedding is not decoration: consequence in the deep
logic can be established entirely by shallow reasoning and transferred back. The
following principle is the bridge used by the protocol tests.\<close>

theorem ConsD_via_shallow:
  assumes shallow: "\<And>W B D V U E w. W w \<Longrightarrow>
      (\<forall>\<gamma>. \<Gamma> \<gamma> \<longrightarrow> (\<forall>v:W. \<langle>W,B,D,V,U,E\<rangle>,v \<Turnstile>\<^sup>s \<lparr>\<gamma>\<rparr>))
        \<Longrightarrow> \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr>"
  shows "\<Gamma> \<Turnstile> \<phi>"
proof (unfold ConsD_def, intro allI impI)
  fix W B D V U E w
  assume sat: "\<forall>\<gamma>. \<Gamma> \<gamma> \<longrightarrow> (\<forall>v:W. \<langle>W,B,D,V,U,E\<rangle>,v \<Turnstile>\<^sup>d \<gamma>)" and wW: "W w"
  have satS: "\<forall>\<gamma>. \<Gamma> \<gamma> \<longrightarrow> (\<forall>v:W. \<langle>W,B,D,V,U,E\<rangle>,v \<Turnstile>\<^sup>s \<lparr>\<gamma>\<rparr>)"
    using sat Faithful1a by blast
  have "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr>" using shallow[OF wW satS] .
  thus "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<phi>" using wW Faithful1a by blast
qed

subsection\<open>The quantifier-scope question, settled\<close>

text\<open>The wide-scope (meta-level) existential of the pre-conditions of question and
challenge implies the narrow-scope (object-level, via \<open>ExJD\<close>) reading.\<close>

lemma ScopeImp:
  assumes "\<exists>\<Delta>. \<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (Done\<^sup>d (Justify i \<Delta> sg \<phi>))))"
  shows "\<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (ExJD i sg \<phi>)))"
proof -
  obtain \<Delta> where H: "\<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (Done\<^sup>d (Justify i \<Delta> sg \<phi>))))" using assms by blast
  show ?thesis unfolding ConsD_def
  proof (intro allI impI)
    fix W B D V U E w
    assume sat: "\<forall>\<gamma>. \<Gamma> \<gamma> \<longrightarrow> (\<forall>w:W. \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<gamma>)" and wW: "W w"
    have "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (Done\<^sup>d (Justify i \<Delta> sg \<phi>))))"
      using H[unfolded ConsD_def] sat wW by blast
    thus "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (ExJD i sg \<phi>)))" by simp blast
  qed
qed

text\<open>The converse fails, and we refute it AT THE LEVEL OF THE CONSEQUENCE RELATION
used by the protocol, not merely pointwise in one model. The refuting situation
needs two distinct worlds; since \<open>\<w>\<close> is only assumed non-empty, this is stated as an
explicit hypothesis. The model was found with \<open>nitpick\<close> \<^cite>\<open>"Nitpick2010"\<close> and is
verified here, so that the entry does not depend on the model finder at build
time: both worlds carry a justification, but for DIFFERENT supports, so no single
\<open>\<Delta>\<close> works globally.\<close>

lemma ScopeConverse_fails:
  fixes \<phi>\<^sub>1 \<phi>\<^sub>2 :: Formula and w\<^sub>1 w\<^sub>2 :: \<w> and i j k::Speaker and sg::Sign and \<phi>::Formula
  assumes distinct\<Delta>: "\<phi>\<^sub>1 \<noteq> \<phi>\<^sub>2" and distinctw: "w\<^sub>1 \<noteq> w\<^sub>2"
  defines "\<Gamma> \<equiv> (\<lambda>x. x = \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (ExJD i sg \<phi>))))"
  shows "(\<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (ExJD i sg \<phi>))))
       \<and> \<not>(\<exists>\<Delta>. \<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (Done\<^sup>d (Justify i \<Delta> sg \<phi>)))))"
proof
  show "\<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (ExJD i sg \<phi>)))" unfolding \<Gamma>_def ConsD_def by blast
next
  let ?W = "\<lambda>w::\<w>. True"
  let ?R = "\<lambda>(x::Speaker) (w::\<w>) (v::\<w>). True"
  let ?U = "\<lambda>l w. l = Justify i (if w = w\<^sub>1 then \<phi>\<^sub>1 else \<phi>\<^sub>2) sg \<phi>"
  have prem: "\<forall>\<gamma>. \<Gamma> \<gamma> \<longrightarrow> (\<forall>w:?W. \<langle>?W,?R,?R,V,?U,E\<rangle>,w \<Turnstile>\<^sup>d \<gamma>)"
    unfolding \<Gamma>_def by auto
  show "\<not>(\<exists>\<Delta>. \<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (Done\<^sup>d (Justify i \<Delta> sg \<phi>)))))"
  proof
    assume "\<exists>\<Delta>. \<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (Done\<^sup>d (Justify i \<Delta> sg \<phi>))))"
    then obtain \<Delta> where
      C: "\<Gamma> \<Turnstile> \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (Done\<^sup>d (Justify i \<Delta> sg \<phi>))))" by blast
    have "\<forall>w:?W. \<langle>?W,?R,?R,V,?U,E\<rangle>,w \<Turnstile>\<^sup>d \<D>\<^sup>d j (\<B>\<^sup>d k (\<D>\<^sup>d j (Done\<^sup>d (Justify i \<Delta> sg \<phi>))))"
      using C[unfolded ConsD_def,
              THEN spec[where x="?W"], THEN spec[where x="?R"], THEN spec[where x="?R"],
              THEN spec[where x=V], THEN spec[where x="?U"], THEN spec[where x=E]] prem by blast
    hence all: "\<And>v. ?U (Justify i \<Delta> sg \<phi>) v" by simp
    have "\<Delta> = \<phi>\<^sub>1" using all[of w\<^sub>1] by simp
    moreover have "\<Delta> = \<phi>\<^sub>2" using all[of w\<^sub>2] distinctw by simp
    ultimately show False using distinct\<Delta> by simp
  qed
qed

subsection\<open>Faithfulness for the minimal embedding, and the comparison\<close>

primrec DpToShMin :: "BDF\<Rightarrow>\<sigma>\<^sub>m" ("\<lceil>_\<rceil>") where
    "\<lceil>x\<^sup>a\<rceil> = x\<^sup>m" | "\<lceil>Done\<^sup>d l\<rceil> = Done\<^sup>m l" | "\<lceil>EntD \<Phi> sg \<phi>\<rceil> = EntM \<Phi> sg \<phi>"
  | "\<lceil>ExJD i sg \<phi>\<rceil> = ExJM i sg \<phi>" | "\<lceil>\<not>\<^sup>d\<phi>\<rceil> = \<not>\<^sup>m\<lceil>\<phi>\<rceil>" | "\<lceil>\<phi> \<supset>\<^sup>d \<psi>\<rceil> = \<lceil>\<phi>\<rceil> \<supset>\<^sup>m \<lceil>\<psi>\<rceil>"
  | "\<lceil>\<B>\<^sup>d i \<phi>\<rceil> = \<B>\<^sup>m i \<lceil>\<phi>\<rceil>" | "\<lceil>\<D>\<^sup>d i \<phi>\<rceil> = \<D>\<^sup>m i \<lceil>\<phi>\<rceil>"

text\<open>Faithfulness for the minimal embedding holds relative to the one fixed,
full-domain model given by the meta-level constants.\<close>

theorem Faithful2:
  "\<forall>w. \<langle>(\<lambda>x::\<w>. True),B\<^sub>0,D\<^sub>0,V\<^sub>0,U\<^sub>0,E\<^sub>0\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<longleftrightarrow> w \<Turnstile>\<^sup>m \<lceil>\<phi>\<rceil>"
  apply (induct \<phi>) by auto

theorem Faithful3:
  "\<forall>w. \<langle>(\<lambda>x::\<w>. True),B\<^sub>0,D\<^sub>0,V\<^sub>0,U\<^sub>0,E\<^sub>0\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr> \<longleftrightarrow> w \<Turnstile>\<^sup>m \<lceil>\<phi>\<rceil>"
  using Faithful1a[of \<phi>] Faithful2[of \<phi>] by auto

text\<open>Minimal validity is sound for deep validity in the following precise sense:
the minimally valid truth sets are exactly the images of the deeply valid
formulas. (This ports lemma Sound1 of FaithfulPMLinHOL, with a structured proof.)\<close>

theorem SoundMin: "(\<Turnstile>\<^sup>m \<psi>) \<longleftrightarrow> (\<exists>\<phi>. \<psi> = \<lceil>\<phi>\<rceil> \<and> \<Turnstile>\<^sup>d \<phi>)"
proof
  assume L: "\<Turnstile>\<^sup>m \<psi>"
  have "\<psi> = \<lceil>p\<^sup>a \<supset>\<^sup>d p\<^sup>a\<rceil>"
  proof (rule ext)
    fix w show "\<psi> w = \<lceil>p\<^sup>a \<supset>\<^sup>d p\<^sup>a\<rceil> w" using L unfolding ValM_def by simp
  qed
  moreover have "\<Turnstile>\<^sup>d (p\<^sup>a \<supset>\<^sup>d p\<^sup>a)" unfolding ValD_def by simp
  ultimately show "\<exists>\<phi>. \<psi> = \<lceil>\<phi>\<rceil> \<and> \<Turnstile>\<^sup>d \<phi>" by blast
next
  assume "\<exists>\<phi>. \<psi> = \<lceil>\<phi>\<rceil> \<and> \<Turnstile>\<^sup>d \<phi>"
  then obtain \<phi> where 1: "\<psi> = \<lceil>\<phi>\<rceil>" and 2: "\<Turnstile>\<^sup>d \<phi>" by blast
  have "\<forall>w. \<langle>(\<lambda>x::\<w>. True),B\<^sub>0,D\<^sub>0,V\<^sub>0,U\<^sub>0,E\<^sub>0\<rangle>,w \<Turnstile>\<^sup>d \<phi>" using 2 unfolding ValD_def by simp
  thus "\<Turnstile>\<^sup>m \<psi>" using 1 Faithful2 unfolding ValM_def by simp
qed

text\<open>Separation of the two shallow backends. Note first a metatheoretical point:
an UNCONDITIONAL refutation of "minimal validity implies deep validity" is not
available, because minimal validity is decided by the uninterpreted constants
\<open>B\<^sub>0,D\<^sub>0,V\<^sub>0,U\<^sub>0,E\<^sub>0\<close>, about which nothing is provable. The separation is therefore
stated conditionally, and this conditionality is itself informative: it says that
the minimal embedding cannot even talk about the models in which its validities
might fail.\<close>

lemma MinimalNotDeep_conditional:
  fixes V::\<V> and w\<^sub>1::\<w>
  assumes minimally_valid: "\<forall>w. V\<^sub>0 x w" and elsewhere_false: "\<not> V x w\<^sub>1"
  shows "\<Turnstile>\<^sup>m \<lceil>x\<^sup>a\<rceil>" and "\<not> \<Turnstile>\<^sup>d x\<^sup>a"
proof -
  show "\<Turnstile>\<^sup>m \<lceil>x\<^sup>a\<rceil>" using minimally_valid unfolding ValM_def by simp
next
  show "\<not> \<Turnstile>\<^sup>d x\<^sup>a"
  proof
    assume A: "\<Turnstile>\<^sup>d x\<^sup>a"
    have "V x w\<^sub>1"
      using A[unfolded ValD_def,
              THEN spec[where x="\<lambda>w::\<w>. True"], THEN spec[where x=B\<^sub>0],
              THEN spec[where x=D\<^sub>0], THEN spec[where x=V],
              THEN spec[where x=U\<^sub>0], THEN spec[where x=E\<^sub>0],
              THEN spec[where x=w\<^sub>1]] by simp
    thus False using elsewhere_false by simp
  qed
qed

subsection\<open>Modal principles proved shallowly, used deeply\<close>

text\<open>The faithfulness theorems are not decoration: modal principles needed by the
protocol are proved on the (maximal) SHALLOW side, where the connectives are plain
HOL definitions and the proofs are immediate, and then transferred to the deep
syntax over which the protocol is defined. The K principle for beliefs and desires
is obtained this way and is used in the tests theory to discharge a pre-condition
that does NOT follow by membership in the world knowledge.\<close>

lemma ShallowK\<B>: "\<Turnstile>\<^sup>s (\<B>\<^sup>s i (\<phi> \<supset>\<^sup>s \<psi>) \<supset>\<^sup>s (\<B>\<^sup>s i \<phi> \<supset>\<^sup>s \<B>\<^sup>s i \<psi>))"
  unfolding ValS_def by auto
lemma ShallowK\<D>: "\<Turnstile>\<^sup>s (\<D>\<^sup>s i (\<phi> \<supset>\<^sup>s \<psi>) \<supset>\<^sup>s (\<D>\<^sup>s i \<phi> \<supset>\<^sup>s \<D>\<^sup>s i \<psi>))"
  unfolding ValS_def by auto

theorem DeepK\<B>: "\<Turnstile>\<^sup>d (\<B>\<^sup>d i (\<phi> \<supset>\<^sup>d \<psi>) \<supset>\<^sup>d (\<B>\<^sup>d i \<phi> \<supset>\<^sup>d \<B>\<^sup>d i \<psi>))"
  using Faithful1b[of "\<B>\<^sup>d i (\<phi> \<supset>\<^sup>d \<psi>) \<supset>\<^sup>d (\<B>\<^sup>d i \<phi> \<supset>\<^sup>d \<B>\<^sup>d i \<psi>)"] ShallowK\<B> by simp
theorem DeepK\<D>: "\<Turnstile>\<^sup>d (\<D>\<^sup>d i (\<phi> \<supset>\<^sup>d \<psi>) \<supset>\<^sup>d (\<D>\<^sup>d i \<phi> \<supset>\<^sup>d \<D>\<^sup>d i \<psi>))"
  using Faithful1b[of "\<D>\<^sup>d i (\<phi> \<supset>\<^sup>d \<psi>) \<supset>\<^sup>d (\<D>\<^sup>d i \<phi> \<supset>\<^sup>d \<D>\<^sup>d i \<psi>)"] ShallowK\<D> by simp

text\<open>Comparison. The maximal embedding threads the whole model through every
formula: validity and the global consequence relation used by the protocol are
genuinely model-quantified, faithfulness (Faithful1a/1b) is unrestricted, and
bounded world domains remain expressible. The minimal embedding is leaner - one
world argument instead of seven parameters - and matches the original
HOMML/FATIO development; but its faithfulness (Faithful2) is relative to the one
fixed full-domain model, so dialogue checking on this backend is checking IN a
situation rather than a logically necessary entailment. Since the protocol layer
is defined over the DEEP syntax, both backends serve it soundly; this entry uses
the maximal one for the protocol's consequence relation and provides the minimal
one, with the bridging theorems above, for lightweight automation and for
continuity with the original sources.\<close>

subsection\<open>A worked illustration of the transfer\<close>

text\<open>An illustration that the shallow backend is usable, not merely present: the
K principle for the belief operator is proved with the shallow definitions (one
call, no induction), and transported to the deep logic by \<open>Faithful1b\<close>. The same
route serves any validity needed while checking dialogues.\<close>

lemma K_shallow: "\<Turnstile>\<^sup>s (\<B>\<^sup>s j (X \<supset>\<^sup>s Y) \<supset>\<^sup>s (\<B>\<^sup>s j X \<supset>\<^sup>s \<B>\<^sup>s j Y))"
  unfolding ValS_def by auto

theorem K_deep: "\<Turnstile>\<^sup>d (\<B>\<^sup>d j (\<phi> \<supset>\<^sup>d \<psi>) \<supset>\<^sup>d (\<B>\<^sup>d j \<phi> \<supset>\<^sup>d \<B>\<^sup>d j \<psi>))"
proof -
  have "\<Turnstile>\<^sup>s \<lparr>\<B>\<^sup>d j (\<phi> \<supset>\<^sup>d \<psi>) \<supset>\<^sup>d (\<B>\<^sup>d j \<phi> \<supset>\<^sup>d \<B>\<^sup>d j \<psi>)\<rparr>"
    using K_shallow[of j "\<lparr>\<phi>\<rparr>" "\<lparr>\<psi>\<rparr>"] by simp
  thus ?thesis using Faithful1b by blast
qed


end
