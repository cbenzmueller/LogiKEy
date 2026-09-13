theory ID_Explanations
  imports ID_Inference
begin

section \<open>Explanations and shared-explanation inference\<close>

text \<open>Explanation definition, conditions 1 and 2, together with E contained in U.
The paper does not impose conflict-freeness here, so neither do we. Defence and
inclusion-minimality are reused from the imported argumentation development.\<close>
definition explanation_support ::
  "'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a Set \<Rightarrow> bool" where
  "explanation_support U att Con p E \<longleftrightarrow>
    E \<subseteq> U \<and> (\<exists>a. E a \<and> Con a = p) \<and>
    (\<forall>a. E a \<longrightarrow> defends_rel U att E a)"

definition explanation ::
  "'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a Set \<Rightarrow> bool" where
  "explanation U att Con p E \<longleftrightarrow> minimal (explanation_support U att Con p) E id"

text \<open>Shared-explanation inference: one explanation is included in every preferred extension.\<close>
definition shared_explanation :: "'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> bool" where
  "shared_explanation U att Con p \<longleftrightarrow>
    (\<exists>E. explanation U att Con p E \<and>
      (\<forall>P. extensions.preferredExt U att P \<longrightarrow> E \<subseteq> P))"

text \<open>The ``strongly agrees because'' definition adds terminology, not a second semantics.\<close>
abbreviation strongly_agrees_because where "strongly_agrees_because \<equiv> shared_explanation"

lemma explanation_iff_no_proper_support:
  "explanation U att Con p E \<longleftrightarrow>
    explanation_support U att Con p E \<and>
    (\<nexists>D. D \<subset> E \<and> explanation_support U att Con p D)"
  unfolding explanation_def minimal_def id_def by blast

lemma explanation_has_support:
  "explanation U att Con p E \<Longrightarrow> explanation_support U att Con p E"
  unfolding explanation_def minimal_def by simp

lemma explanation_has_conclusion:
  assumes expl: "explanation U att Con p E"
  shows "\<exists>a. E a \<and> proximal_explanation U Con p a"
  using explanation_has_support[OF expl]
  unfolding explanation_support_def proximal_explanation_def by blast

lemma shared_explanation_imp_shared_argument:
  assumes shared: "shared_explanation U att Con p"
  shows "shared_argument U att Con p"
  using explanation_has_conclusion shared shared_argument_def shared_explanation_def by fastforce


text \<open>Proposition 2, and the positive part of Proposition 1.\<close>
theorem agreement_hierarchy:
  assumes strong: "shared_explanation U att Con p"
  shows "shared_argument U att Con p \<and> shared_conclusion U att Con p \<and>
    credulous_conclusion U att Con p"
  by (simp add: shared_argument_imp_shared_conclusion shared_conclusion_imp_credulous
      shared_explanation_imp_shared_argument strong)

lemma explanation_support_induced [simp]:
  "explanation_support U (induced_att att U) Con p E = explanation_support U att Con p E"
  unfolding explanation_support_def defends_rel_def induced_att_def by blast

lemma explanation_induced [simp]:
  "explanation U (induced_att att U) Con p E = explanation U att Con p E"
  unfolding explanation_def minimal_def by simp

lemma shared_explanation_induced [simp]:
  "shared_explanation U (induced_att att U) Con p = shared_explanation U att Con p"
  unfolding shared_explanation_def by simp

lemma shared_explanation_has_admissible_witness:
  assumes "shared_explanation U att Con p"
  shows "\<exists>E. explanation U att Con p E \<and> extensions.admissibleExt U att E"
  by (smt (verit) admissibleExt_def agreement_hierarchy assms credulous_conclusion_def explanation_has_support
      explanation_support_def preferredConflictfree shared_explanation_def)

text \<open>Correspondence with ideal semantics. For finite U, shared-explanation
inference holds exactly when some ideal set contains an argument concluding p,
equivalently when an argument in the ideal extension concludes p. Closure of
ideal sets under union is provided by idealSetUnion in ext-properties. The
forward implication needs no finiteness assumption; the converse uses finite U
to extract a minimal explanation from an ideal set.\<close>

lemma shared_explanation_imp_idealset:
  assumes se: "shared_explanation U att Con p"
  shows "\<exists>E. extensions.idealSet U att E \<and> (\<exists>a. U a \<and> E a \<and> Con a = p)"
proof -
  from se obtain E where exp: "explanation U att Con p E"
    and sub: "\<forall>P. extensions.preferredExt U att P \<longrightarrow> E \<subseteq> P"
    unfolding shared_explanation_def by blast
  have supp: "explanation_support U att Con p E"
    by (rule explanation_has_support[OF exp])
  have EU: "\<forall>a. E a \<longrightarrow> U a" and conc: "\<exists>a. E a \<and> Con a = p"
    and defd: "\<forall>a. E a \<longrightarrow> defends_rel U att E a"
    using supp unfolding explanation_support_def by auto
  obtain P where P: "extensions.preferredExt U att P"
    by (metis preferredExist preferredExt_defEq extensions.preferredExt2_def)
  have "E \<subseteq> P" using sub P by blast
  hence cf: "extensions.conflictfreeExt U att E"
    using preferredConflictfree[OF subs_rel] P by blast
  have adm: "extensions.admissibleExt U att E"
    unfolding admissibleExt_def using cf defd by blast
  have subU: "\<forall>Q. extensions.preferredExt U att Q \<longrightarrow> E \<subseteq>\<^sup>U Q"
    using sub subs_rel by blast
  have "extensions.idealSet U att E"
    unfolding idealSet_def using adm subU by blast
  thus ?thesis using conc EU by blast
qed

text \<open>Extraction of a minimal explanation from any support, for finite U
(induction on the cardinality of the support).\<close>
lemma minimal_support_extract_n:
  assumes fin: "finite {a. U a}"
  shows "card {a. S a} = n \<Longrightarrow> S \<subseteq> U \<Longrightarrow> explanation_support U att Con p S
         \<Longrightarrow> \<exists>E. explanation U att Con p E \<and> E \<subseteq> S"
proof (induct n arbitrary: S rule: less_induct)
  case (less n S)
  from less.prems have cardn: "card {a. S a} = n" and SU: "S \<subseteq> U"
    and supp: "explanation_support U att Con p S" by auto
  show ?case
  proof (cases "\<exists>X. explanation_support U att Con p X \<and> X \<subseteq> S \<and> \<not> (X \<approx> S)")
    case False
    hence "explanation U att Con p S"
      using supp unfolding explanation_def minimal_def by (auto simp: id_def)
    thus ?thesis by blast
  next
    case True
    then obtain X where X1: "explanation_support U att Con p X" and X2: "X \<subseteq> S"
      and X3: "\<not> (X \<approx> S)" by blast
    have XU: "X \<subseteq> U" using X2 SU by auto
    have finS: "finite {a. S a}"
      using fin SU by (metis (mono_tags) Collect_mono mem_Collect_eq rev_finite_subset)
    have "card {a. X a} < card {a. S a}"
    proof -
      have ne: "{a. X a} \<noteq> {a. S a}" using X3 by auto
      have mono: "\<forall>x. X x \<longrightarrow> S x" using X2 by auto
      show ?thesis using finS ne mono
        by (metis (mono_tags, lifting) Collect_mono mem_Collect_eq psubsetI psubset_card_mono)
    qed
    hence "card {a. X a} < n" using cardn by simp
    from less.hyps[OF this refl XU X1] obtain E
      where "explanation U att Con p E" "E \<subseteq> X" by blast
    thus ?thesis using X2 by auto
  qed
qed

lemma minimal_support_extract:
  assumes fin: "finite {a. U a}" and SU: "S \<subseteq> U"
    and supp: "explanation_support U att Con p S"
  shows "\<exists>E. explanation U att Con p E \<and> E \<subseteq> S"
  using minimal_support_extract_n[OF fin refl SU supp] .

text \<open>Converse direction (finite U): a concluder in an ideal set yields
shared-explanation inference.\<close>
lemma idealset_imp_shared_explanation:
  assumes fin: "finite {a. U a}"
    and I: "extensions.idealSet U att I"
    and conc: "\<exists>a. U a \<and> I a \<and> Con a = p"
  shows "shared_explanation U att Con p"
proof -
  define I' where "I' = (\<lambda>x. U x \<and> I x)"
  have I'sub: "I' \<subseteq> U" unfolding I'_def by auto
  have adm: "extensions.admissibleExt U att I"
    using I unfolding idealSet_def by auto
  have conc': "\<exists>a. I' a \<and> Con a = p" using conc unfolding I'_def by auto
  have defd': "\<forall>a. I' a \<longrightarrow> defends_rel U att I' a"
  proof (intro allI impI)
    fix a assume "I' a"
    hence Ua: "U a" and Ia: "I a" unfolding I'_def by auto
    have "defends_rel U att I a" using adm Ua Ia unfolding admissibleExt_def by auto
    thus "defends_rel U att I' a" unfolding defends_rel_def I'_def by auto
  qed
  have supp': "explanation_support U att Con p I'"
    unfolding explanation_support_def using I'sub conc' defd' by auto
  obtain E where E: "explanation U att Con p E" and EsubI': "E \<subseteq> I'"
    using minimal_support_extract[OF fin I'sub supp'] by blast
  have IsubPref: "\<forall>P. extensions.preferredExt U att P \<longrightarrow> I \<subseteq>\<^sup>U P"
    using I unfolding idealSet_def by auto
  have EsubI: "\<forall>x. E x \<longrightarrow> U x \<and> I x" using EsubI' unfolding I'_def by auto
  have "\<forall>P. extensions.preferredExt U att P \<longrightarrow> E \<subseteq> P"
    using IsubPref EsubI by blast
  thus ?thesis unfolding shared_explanation_def using E by blast
qed

text \<open>Full correspondence (finite U): shared-explanation inference iff some
argument concluding p lies in an ideal set.\<close>
theorem shared_explanation_iff_idealset:
  assumes fin: "finite {a. U a}"
  shows "shared_explanation U att Con p
         \<longleftrightarrow> (\<exists>E. extensions.idealSet U att E \<and> (\<exists>a. U a \<and> E a \<and> Con a = p))"
proof
  assume "shared_explanation U att Con p"
  thus "\<exists>E. extensions.idealSet U att E \<and> (\<exists>a. U a \<and> E a \<and> Con a = p)"
    by (rule shared_explanation_imp_idealset)
next
  assume "\<exists>E. extensions.idealSet U att E \<and> (\<exists>a. U a \<and> E a \<and> Con a = p)"
  then obtain E where E: "extensions.idealSet U att E"
    and c: "\<exists>a. U a \<and> E a \<and> Con a = p" by blast
  show "shared_explanation U att Con p"
    using idealset_imp_shared_explanation[OF fin E c] .
qed

text \<open>Bounded regression check of the correspondence for argument types of
sizes 1--4 and conclusion types of sizes 1--3. The query requires the outcome
\<open>none\<close>; a counterexample or inconclusive result fails the check. The statement
is discarded after the search. The general finite-universe result is proved above.\<close>
lemma shared_explanation_iff_idealset_nitpick:
  "finite {a. U a} \<longrightarrow>
     (shared_explanation U att Con p
      \<longleftrightarrow> (\<exists>E. extensions.idealSet U att E \<and> (\<exists>a. U a \<and> E a \<and> Con a = p)))"
  nitpick[card 'a = 1-4, card 'c = 1-3, timeout = 120, expect = none]
  oops

end
