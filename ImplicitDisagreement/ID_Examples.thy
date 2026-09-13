theory ID_Examples
  imports ID_Disagreement
begin

text \<open>A two-argument counterexample to the converse of Proposition 1.
Both arguments conclude the same formula, but attack each other. This small
example isolates the difference between shared conclusion and shared argument.\<close>
definition mutual_attack :: "bool Rel" where
  "mutual_attack a b \<longleftrightarrow> a \<noteq> b"

lemma bool_all: "(\<forall>x::bool. P x) \<longleftrightarrow> P False \<and> P True" 
  by metis

lemma bool_ex: "(\<exists>x::bool. P x) \<longleftrightarrow> P False \<or> P True"
  by metis

lemma bool_predicate_cases:
  "P = (\<lambda>(_::bool). False) \<or> P = id \<or> P = Not \<or> P = (\<lambda>_. True)"
  by (cases "P False"; cases "P True"; auto simp: fun_eq_iff bool_all)

lemma bool_predicate_all:
  "(\<forall>P::bool \<Rightarrow> bool. Q P) \<longleftrightarrow>
    Q (\<lambda>_. False) \<and> Q id \<and> Q Not \<and> Q (\<lambda>_. True)" 
  by (metis (lifting) ext bool_predicate_cases)

lemma mutual_complete:
  "extensions.completeExt (\<lambda>_. True) mutual_attack E \<longleftrightarrow>
    \<not> (E False \<and> E True)"
  unfolding extensions.completeExt_def extensions.admissibleExt_def
    extensions.conflictfreeExt_def defends_rel_def mutual_attack_def
  by (auto simp: bool_all bool_ex)

lemma mutual_preferred:
  "extensions.preferredExt (\<lambda>_. True) mutual_attack E \<longleftrightarrow>
    (E False \<noteq> E True)"
  unfolding extensions.preferredExt_def maximal_rel_def mutual_complete id_def
  by (auto simp: bool_predicate_all bool_all)

lemma shared_conclusion_without_shared_argument:
  "shared_conclusion (\<lambda>_. True) mutual_attack (\<lambda>_. ()) () \<and>
    \<not> shared_argument (\<lambda>_. True) mutual_attack (\<lambda>_. ()) ()"
  unfolding shared_conclusion_def shared_argument_def proximal_explanation_def
  by (auto simp: mutual_preferred bool_predicate_all bool_all bool_ex)

lemma proximal_disagreement_is_not_ordinary_disagreement:
  "proximal_disagreement (\<lambda>_. True) mutual_attack (\<lambda>_. ()) () \<and>
    distal_disagreement (\<lambda>_. True) mutual_attack (\<lambda>_. ()) () \<and>
    \<not> disagrees_that (\<lambda>_. True) mutual_attack (\<lambda>_. ()) ()"
  by (metis agreement_hierarchy distal_disagreement_def ordinary_and_distal_disjoint proximal_disagreement_def
      shared_conclusion_without_shared_argument)

text \<open>The Explanation definition really permits a conflicting explanation. With one
self-attacking argument the singleton is a minimal self-defending support.
It is not a shared explanation, because the only preferred In-set is empty.\<close>
lemma self_attacking_explanation:
  "explanation (\<lambda>_. True) (\<lambda>(_::unit) _. True) (\<lambda>_. ()) () (\<lambda>_. True)"
  unfolding explanation_def minimal_def explanation_support_def defends_rel_def id_def
  by auto

lemma self_attacking_explanation_is_conflicting:
  "\<not> extensions.conflictfreeExt (\<lambda>_. True) (\<lambda>(_::unit) _. True) (\<lambda>_. True)"
  unfolding extensions.conflictfreeExt_def by simp

text \<open>A coalition introduces an edge that neither singleton agent can see.
This also corrects Example 4: for the sole edge a attacks b, a survives.\<close>
definition one_way_attack :: "bool Rel" where
  "one_way_attack a b \<longleftrightarrow> \<not> a \<and> b"

lemma coalition_reveals_cross_edge:
  "\<not> induced_att one_way_attack (\<lambda>x. \<not> x) False True \<and>
   \<not> induced_att one_way_attack (\<lambda>x. x) False True \<and>
   coalition_att one_way_attack (\<lambda>x. \<not> x) (\<lambda>x. x) False True"
  unfolding induced_att_def one_way_attack_def by simp

lemma one_way_preferred:
  "extensions.preferredExt (\<lambda>_. True) one_way_attack E \<longleftrightarrow>
    E False \<and> \<not> E True"
  unfolding extensions.preferredExt_def maximal_rel_def extensions.completeExt_def
    extensions.admissibleExt_def extensions.conflictfreeExt_def defends_rel_def
    one_way_attack_def id_def
  by (auto simp: bool_all bool_ex)

lemma one_way_coalition_keeps_attacker:
  "shared_argument (\<lambda>_. True) one_way_attack id False \<and>
    \<not> credulous_conclusion (\<lambda>_. True) one_way_attack id True"
  unfolding shared_argument_def credulous_conclusion_def proximal_explanation_def
  by (auto simp: one_way_preferred bool_all bool_ex)

text \<open>The six-argument running-example graph (the bioethics and
constitutional-law readings share it). Optional datatype plugins are disabled
to avoid generating admitted Quickcheck support equations.
The conclusion of A1 is represented by True; the other arguments conclude False.
Only equality of conclusions is used, so this is a model of the designated issue,
not a formalization of the internal bioethical or constitutional arguments.\<close>
datatype (plugins only: code) bio_argument = A1 | A2 | A3 | A4 | A5 | A6

definition bio_att :: "bio_argument Rel" where
  "bio_att a b \<longleftrightarrow>
    (a = A2 \<and> b = A1) \<or> (a = A3 \<and> b = A2) \<or>
    (a = A4 \<and> b = A2) \<or> (a = A5 \<and> b = A4) \<or>
    (a = A6 \<and> b = A3) \<or> (a = A5 \<and> b = A6) \<or>
    (a = A6 \<and> b = A5)"

abbreviation bio_con where "bio_con a \<equiv> a = A1"
abbreviation bio_left where "bio_left \<equiv> \<lbrace>A1,A3,A5\<rbrace>"
abbreviation bio_right where "bio_right \<equiv> \<lbrace>A1,A4,A6\<rbrace>"
abbreviation bio_left_agent where "bio_left_agent \<equiv> bio_left \<union> \<lbrace>A2\<rbrace>"
abbreviation bio_right_agent where "bio_right_agent \<equiv> bio_right \<union> \<lbrace>A2\<rbrace>"

lemma bio_all:
  "(\<forall>x::bio_argument. P x) \<longleftrightarrow>
    P A1 \<and> P A2 \<and> P A3 \<and> P A4 \<and> P A5 \<and> P A6" 
  by (metis bio_argument.exhaust)

lemma bio_ex:
  "(\<exists>x::bio_argument. P x) \<longleftrightarrow>
    P A1 \<or> P A2 \<or> P A3 \<or> P A4 \<or> P A5 \<or> P A6"
  by (metis bio_argument.exhaust)

lemma bio_agents_wellformed:
  "is_agent (\<lambda>_. True) bio_att bio_left_agent (induced_att bio_att bio_left_agent) \<and>
    is_agent (\<lambda>_. True) bio_att bio_right_agent (induced_att bio_att bio_right_agent)"
  unfolding is_agent_def by simp

lemma bio_coalition_all: "coalition bio_left_agent bio_right_agent = (\<lambda>_. True)"
  by (auto simp: fun_eq_iff bio_all)

lemma bio_agents_share_conclusion:
  "shared_conclusion bio_left_agent bio_att bio_con True"
  "shared_conclusion bio_right_agent bio_att bio_con True" 
proof -
  have left: "E A1" if "extensions.preferredExt bio_left_agent bio_att E" for E
  proof -
    have "extensions.completeExt bio_left_agent bio_att E"
      using that unfolding extensions.preferredExt_def maximal_rel_def by blast
    then show ?thesis
      unfolding extensions.completeExt_def extensions.admissibleExt_def
        extensions.conflictfreeExt_def defends_rel_def bio_att_def
      by (auto simp: bio_all bio_ex)
  qed
  have right: "E A1" if "extensions.preferredExt bio_right_agent bio_att E" for E
  proof -
    have "extensions.completeExt bio_right_agent bio_att E"
      using that unfolding extensions.preferredExt_def maximal_rel_def by blast
    then show ?thesis
      unfolding extensions.completeExt_def extensions.admissibleExt_def
        extensions.conflictfreeExt_def defends_rel_def bio_att_def
      by (auto simp: bio_all bio_ex)
  qed
  show "shared_conclusion bio_left_agent bio_att bio_con True"
    using left unfolding shared_conclusion_def proximal_explanation_def
    by (auto simp: bio_ex)
  show "shared_conclusion bio_right_agent bio_att bio_con True"
    using right unfolding shared_conclusion_def proximal_explanation_def
    by (auto simp: bio_ex)
qed

lemma bio_complete:
  "extensions.completeExt (\<lambda>_. True) bio_att E \<longleftrightarrow>
    (E \<approx> (\<lambda>_. False)) \<or> E \<approx> bio_left \<or> E \<approx> bio_right"
  unfolding extensions.completeExt_def extensions.admissibleExt_def
    extensions.conflictfreeExt_def defends_rel_def bio_att_def
  by (auto simp: bio_all bio_ex; blast)

lemma bio_left_preferred: "extensions.preferredExt (\<lambda>_. True) bio_att bio_left"
  unfolding extensions.preferredExt_def maximal_rel_def bio_complete id_def
  by (auto simp: bio_all)

lemma bio_right_preferred: "extensions.preferredExt (\<lambda>_. True) bio_att bio_right"
  unfolding extensions.preferredExt_def maximal_rel_def bio_complete id_def
  by (auto simp: bio_all)

lemma bio_preferred:
  "extensions.preferredExt (\<lambda>_. True) bio_att E \<longleftrightarrow>
    E \<approx> bio_left \<or> E \<approx> bio_right"
proof
  assume pref: "extensions.preferredExt (\<lambda>_. True) bio_att E"
  have comp: "extensions.completeExt (\<lambda>_. True) bio_att E"
    using pref unfolding extensions.preferredExt_def maximal_rel_def by blast
  have left_comp: "extensions.completeExt (\<lambda>_. True) bio_att bio_left"
    using bio_left_preferred unfolding extensions.preferredExt_def maximal_rel_def by blast
  have nonempty: "\<not> E \<approx> (\<lambda>_. False)"
  proof
    assume empty: "E \<approx> (\<lambda>_. False)"
    have sub: "E \<subseteq> bio_left" using empty by blast
    have "bio_left \<approx> E"
      using pref left_comp sub
      unfolding extensions.preferredExt_def maximal_rel_def id_def by blast
    then show False using empty by (auto simp: bio_all)
  qed
  show "E \<approx> bio_left \<or> E \<approx> bio_right"
    using comp nonempty by (auto simp: bio_complete)
next
  assume "E \<approx> bio_left \<or> E \<approx> bio_right"
  then have "E = bio_left \<or> E = bio_right" by (auto simp: fun_eq_iff)
  then show "extensions.preferredExt (\<lambda>_. True) bio_att E"
    using bio_left_preferred bio_right_preferred by auto
qed

lemma bio_shared_argument: "shared_argument (\<lambda>_. True) bio_att bio_con True"
  unfolding shared_argument_def proximal_explanation_def
  by (auto simp: bio_preferred bio_all bio_ex)

lemma bio_no_shared_explanation: "\<not> shared_explanation (\<lambda>_. True) bio_att bio_con True"
proof
  assume strong: "shared_explanation (\<lambda>_. True) bio_att bio_con True"
  obtain E where expl: "explanation (\<lambda>_. True) bio_att bio_con True E"
    and shared: "\<forall>P. extensions.preferredExt (\<lambda>_. True) bio_att P \<longrightarrow> E \<subseteq> P"
    using strong unfolding shared_explanation_def by blast
  have support: "explanation_support (\<lambda>_. True) bio_att bio_con True E"
    by (rule explanation_has_support[OF expl])
  have left: "E \<subseteq> bio_left"
    using shared[rule_format, OF bio_left_preferred] by blast
  have right: "E \<subseteq> bio_right"
    using shared[rule_format, OF bio_right_preferred] by blast
  have member: "E A1"
    using support unfolding explanation_support_def by (auto simp: bio_ex)
  have defended: "defends_rel (\<lambda>_. True) bio_att E A1"
    using support member unfolding explanation_support_def by blast
  have no_defender: "\<not> E A3 \<and> \<not> E A4"
    using left right by (auto simp: bio_all)
  show False using defended no_defender
    unfolding defends_rel_def bio_att_def by (auto simp: bio_all bio_ex)
qed

lemma bio_distal_but_not_proximal:
  "distal_disagreement (\<lambda>_. True) bio_att bio_con True \<and>
    \<not> proximal_disagreement (\<lambda>_. True) bio_att bio_con True"
proof -
  have agreed: "shared_conclusion (\<lambda>_. True) bio_att bio_con True"
    by (rule shared_argument_imp_shared_conclusion[OF bio_shared_argument])
  show ?thesis using agreed bio_shared_argument bio_no_shared_explanation
    unfolding distal_disagreement_def proximal_disagreement_def by blast
qed

lemma bio_A1_not_weak_spot: "\<not> weak_spot (\<lambda>_. True) bio_att bio_con True A1"
  by (rule removing_the_only_concluder_is_not_a_weak_spot) simp

lemma bio_potential_and_actual_distal:
  "potential_distal_disagreement bio_left_agent bio_right_agent bio_att bio_con True \<and>
    distal_implicit_disagreement bio_left_agent bio_right_agent bio_att bio_con True"
proof -
  have no_shared:
    "\<not> shared_explanation (coalition bio_left_agent bio_right_agent) bio_att bio_con True"
    by (subst bio_coalition_all, rule bio_no_shared_explanation)
  have distal:
    "distal_disagreement (coalition bio_left_agent bio_right_agent) bio_att bio_con True"
    by (subst bio_coalition_all, rule conjunct1[OF bio_distal_but_not_proximal])
  show ?thesis using bio_agents_share_conclusion no_shared distal
    unfolding potential_distal_disagreement_def by blast
qed

text \<open>The paper's weak-spot analysis: removing A3 (or A4) turns the shared
conclusion of A1 into ordinary disagreement. After deleting A3 the preferred
extensions are, restricted to the remaining universe, exactly the patterns
below: one still supports A1, the other does not.\<close>

text \<open>The deleted-argument universes are proper definitions, not abbreviations:
an opaque constant keeps higher-order rewriting with the characterization
lemmas first-order, so the preferred-extension proofs stay one-liners. The
membership lemma lets applied occurrences still compute.\<close>

definition bio_minus :: "bio_argument \<Rightarrow> bio_argument Set" where
  "bio_minus a = remove_argument (\<lambda>_. True) a"

lemma bio_minus_mem [simp]: "bio_minus a x \<longleftrightarrow> x \<noteq> a"
  unfolding bio_minus_def by simp

lemma bio_minus3_complete:
  "extensions.completeExt (bio_minus A3) bio_att E \<longleftrightarrow>
     (\<not> E A1 \<and> \<not> E A2 \<and> \<not> E A4 \<and> \<not> E A5 \<and> \<not> E A6) \<or>
     (\<not> E A1 \<and> E A2 \<and> \<not> E A4 \<and> E A5 \<and> \<not> E A6) \<or>
     (E A1 \<and> \<not> E A2 \<and> E A4 \<and> \<not> E A5 \<and> E A6)"
  unfolding extensions.completeExt_def extensions.admissibleExt_def
    extensions.conflictfreeExt_def defends_rel_def bio_att_def
  by (auto simp: bio_all bio_ex; blast)

lemma bio_minus3_left_preferred:
  "extensions.preferredExt (bio_minus A3) bio_att \<lbrace>A2,A5\<rbrace>"
  unfolding extensions.preferredExt_def maximal_rel_def id_def
  by (auto simp: bio_minus3_complete bio_all)

lemma bio_minus3_right_preferred:
  "extensions.preferredExt (bio_minus A3) bio_att \<lbrace>A1,A4,A6\<rbrace>"
  unfolding extensions.preferredExt_def maximal_rel_def id_def
  by (auto simp: bio_minus3_complete bio_all)

lemma bio_A3_weak_spot: "weak_spot (\<lambda>_. True) bio_att bio_con True A3"
proof -
  have shared: "shared_conclusion (\<lambda>_. True) bio_att bio_con True"
    by (rule shared_argument_imp_shared_conclusion[OF bio_shared_argument])
  have cred: "credulous_conclusion (bio_minus A3) bio_att bio_con True"
    unfolding credulous_conclusion_def proximal_explanation_def
    using bio_minus3_right_preferred by fastforce
  have nshared: "\<not> shared_conclusion (bio_minus A3) bio_att bio_con True"
    unfolding shared_conclusion_def proximal_explanation_def
    using bio_minus3_left_preferred by (auto simp: bio_ex)
  show ?thesis
    unfolding weak_spot_def disagrees_that_def bio_minus_def[symmetric]
    using shared cred nshared by simp
qed

lemma bio_minus4_complete:
  "extensions.completeExt (bio_minus A4) bio_att E \<longleftrightarrow>
     (\<not> E A1 \<and> \<not> E A2 \<and> \<not> E A3 \<and> \<not> E A5 \<and> \<not> E A6) \<or>
     (\<not> E A1 \<and> E A2 \<and> \<not> E A3 \<and> \<not> E A5 \<and> E A6) \<or>
     (E A1 \<and> \<not> E A2 \<and> E A3 \<and> E A5 \<and> \<not> E A6)"
  unfolding extensions.completeExt_def extensions.admissibleExt_def
    extensions.conflictfreeExt_def defends_rel_def bio_att_def
  by (auto simp: bio_all bio_ex; blast)

lemma bio_minus4_left_preferred:
  "extensions.preferredExt (bio_minus A4) bio_att \<lbrace>A2,A6\<rbrace>"
  unfolding extensions.preferredExt_def maximal_rel_def id_def
  by (auto simp: bio_minus4_complete bio_all)

lemma bio_minus4_right_preferred:
  "extensions.preferredExt (bio_minus A4) bio_att \<lbrace>A1,A3,A5\<rbrace>"
  unfolding extensions.preferredExt_def maximal_rel_def id_def
  by (auto simp: bio_minus4_complete bio_all)

lemma bio_A4_weak_spot: "weak_spot (\<lambda>_. True) bio_att bio_con True A4"
proof -
  have shared: "shared_conclusion (\<lambda>_. True) bio_att bio_con True"
    by (rule shared_argument_imp_shared_conclusion[OF bio_shared_argument])
  have cred: "credulous_conclusion (bio_minus A4) bio_att bio_con True"
    unfolding credulous_conclusion_def proximal_explanation_def
    using bio_minus4_right_preferred by fastforce
  have nshared: "\<not> shared_conclusion (bio_minus A4) bio_att bio_con True"
    unfolding shared_conclusion_def proximal_explanation_def
    using bio_minus4_left_preferred by (auto simp: bio_ex)
  show ?thesis
    unfolding weak_spot_def disagrees_that_def bio_minus_def[symmetric]
    using shared cred nshared by simp
qed

text \<open>The paper's antagonists: removing A2, A5 or A6 turns the distal
disagreement into agreement from a shared explanation. In each case an
explicit explanation is contained in every preferred extension of the
reduced framework.\<close>

lemma bio_A2_antagonist: "antagonist (\<lambda>_. True) bio_att bio_con True A2"
proof -
  have expl: "explanation (bio_minus A2) bio_att bio_con True \<lbrace>A1\<rbrace>"
    unfolding explanation_def minimal_def explanation_support_def defends_rel_def id_def
    by (auto simp: bio_att_def bio_all bio_ex)
  have inall: "\<lbrace>A1\<rbrace> \<subseteq> P" if "extensions.preferredExt (bio_minus A2) bio_att P" for P
  proof -
    have "extensions.completeExt (bio_minus A2) bio_att P"
      using that unfolding extensions.preferredExt_def maximal_rel_def by blast
    then show ?thesis
      unfolding extensions.completeExt_def extensions.admissibleExt_def
        extensions.conflictfreeExt_def defends_rel_def bio_att_def
      by (auto simp: bio_all bio_ex)
  qed
  have sh: "shared_explanation (bio_minus A2) bio_att bio_con True"
    unfolding shared_explanation_def using expl inall by blast
  show ?thesis
    unfolding antagonist_def bio_minus_def[symmetric]
    using conjunct1[OF bio_distal_but_not_proximal] sh by simp
qed

lemma bio_A5_antagonist: "antagonist (\<lambda>_. True) bio_att bio_con True A5"
proof -
  have expl: "explanation (bio_minus A5) bio_att bio_con True \<lbrace>A1,A4\<rbrace>"
    unfolding explanation_def minimal_def explanation_support_def defends_rel_def id_def
    by (auto simp: bio_att_def bio_all bio_ex)
  have inall: "\<lbrace>A1,A4\<rbrace> \<subseteq> P" if "extensions.preferredExt (bio_minus A5) bio_att P" for P
  proof -
    have comp: "extensions.completeExt (bio_minus A5) bio_att P"
      using that unfolding extensions.preferredExt_def maximal_rel_def by blast
    have p4: "P A4"
      using comp unfolding extensions.completeExt_def extensions.admissibleExt_def
        extensions.conflictfreeExt_def defends_rel_def bio_att_def
      by (auto simp: bio_all bio_ex)
    have p1: "P A1"
      using comp p4 unfolding extensions.completeExt_def extensions.admissibleExt_def
        extensions.conflictfreeExt_def defends_rel_def bio_att_def
      by (auto simp: bio_all bio_ex)
    show ?thesis using p1 p4 by (auto simp: bio_all)
  qed
  have sh: "shared_explanation (bio_minus A5) bio_att bio_con True"
    unfolding shared_explanation_def using expl inall by blast
  show ?thesis
    unfolding antagonist_def bio_minus_def[symmetric]
    using conjunct1[OF bio_distal_but_not_proximal] sh by simp
qed

lemma bio_A6_antagonist: "antagonist (\<lambda>_. True) bio_att bio_con True A6"
proof -
  have expl: "explanation (bio_minus A6) bio_att bio_con True \<lbrace>A1,A3\<rbrace>"
    unfolding explanation_def minimal_def explanation_support_def defends_rel_def id_def
    by (auto simp: bio_att_def bio_all bio_ex)
  have inall: "\<lbrace>A1,A3\<rbrace> \<subseteq> P" if "extensions.preferredExt (bio_minus A6) bio_att P" for P
  proof -
    have comp: "extensions.completeExt (bio_minus A6) bio_att P"
      using that unfolding extensions.preferredExt_def maximal_rel_def by blast
    have p3: "P A3"
      using comp unfolding extensions.completeExt_def extensions.admissibleExt_def
        extensions.conflictfreeExt_def defends_rel_def bio_att_def
      by (auto simp: bio_all bio_ex)
    have p1: "P A1"
      using comp p3 unfolding extensions.completeExt_def extensions.admissibleExt_def
        extensions.conflictfreeExt_def defends_rel_def bio_att_def
      by (auto simp: bio_all bio_ex)
    show ?thesis using p1 p3 by (auto simp: bio_all)
  qed
  have sh: "shared_explanation (bio_minus A6) bio_att bio_con True"
    unfolding shared_explanation_def using expl inall by blast
  show ?thesis
    unfolding antagonist_def bio_minus_def[symmetric]
    using conjunct1[OF bio_distal_but_not_proximal] sh by simp
qed

text \<open>The coalition-only example of the paper's Section 3:
each agent's own argument (CE resp.\ CF) defeats its defender of CA, so
neither agent accepts CA individually. In the coalition CE and CF attack
each other, every preferred extension keeps exactly one of them, and CA is
accepted in all of them---yet no explanation is shared. This yields distal
implicit disagreement that is not potential disagreement.\<close>

datatype (plugins only: code) co_argument = CA | CB | CE | CF | CG | CH

definition co_att :: "co_argument Rel" where
  "co_att a b \<longleftrightarrow>
    (a = CB \<and> b = CA) \<or> (a = CG \<and> b = CB) \<or> (a = CH \<and> b = CB) \<or>
    (a = CE \<and> b = CG) \<or> (a = CF \<and> b = CH) \<or>
    (a = CE \<and> b = CF) \<or> (a = CF \<and> b = CE)"

abbreviation co_con :: "co_argument \<Rightarrow> bool" where "co_con a \<equiv> a = CA"

definition co_alpha :: "co_argument Set" where
  "co_alpha = \<lbrace>CA,CB\<rbrace> \<union> \<lbrace>CE,CG\<rbrace>"

definition co_beta :: "co_argument Set" where
  "co_beta = \<lbrace>CA,CB\<rbrace> \<union> \<lbrace>CF,CH\<rbrace>"

lemma co_alpha_mem [simp]: "co_alpha x \<longleftrightarrow> x = CA \<or> x = CB \<or> x = CE \<or> x = CG"
  unfolding co_alpha_def by auto

lemma co_beta_mem [simp]: "co_beta x \<longleftrightarrow> x = CA \<or> x = CB \<or> x = CF \<or> x = CH"
  unfolding co_beta_def by auto

abbreviation co_left where "co_left \<equiv> \<lbrace>CA,CE,CH\<rbrace>"
abbreviation co_right where "co_right \<equiv> \<lbrace>CA,CF,CG\<rbrace>"

lemma co_all:
  "(\<forall>x::co_argument. P x) \<longleftrightarrow>
    P CA \<and> P CB \<and> P CE \<and> P CF \<and> P CG \<and> P CH"
  by (metis co_argument.exhaust)

lemma co_ex:
  "(\<exists>x::co_argument. P x) \<longleftrightarrow>
    P CA \<or> P CB \<or> P CE \<or> P CF \<or> P CG \<or> P CH"
  by (metis co_argument.exhaust)

lemma co_agents_wellformed:
  "is_agent (\<lambda>_. True) co_att co_alpha (induced_att co_att co_alpha) \<and>
    is_agent (\<lambda>_. True) co_att co_beta (induced_att co_att co_beta)"
  unfolding is_agent_def by simp

lemma co_coalition_all: "coalition co_alpha co_beta = (\<lambda>_. True)"
  by (auto simp: fun_eq_iff co_all)

lemma co_alpha_complete:
  "extensions.completeExt co_alpha co_att E \<longleftrightarrow>
     (\<not> E CA \<and> E CB \<and> E CE \<and> \<not> E CG)"
  unfolding extensions.completeExt_def extensions.admissibleExt_def
    extensions.conflictfreeExt_def defends_rel_def co_att_def
  by (auto simp: co_all co_ex)

lemma co_beta_complete:
  "extensions.completeExt co_beta co_att E \<longleftrightarrow>
     (\<not> E CA \<and> E CB \<and> E CF \<and> \<not> E CH)"
  unfolding extensions.completeExt_def extensions.admissibleExt_def
    extensions.conflictfreeExt_def defends_rel_def co_att_def
  by (auto simp: co_all co_ex)

lemma co_agents_reject:
  "\<not> shared_conclusion co_alpha co_att co_con True \<and>
    \<not> shared_conclusion co_beta co_att co_con True"
proof -
  have a: "\<not> shared_conclusion co_alpha co_att co_con True"
  proof
    assume sh: "shared_conclusion co_alpha co_att co_con True"
    obtain E where pref: "extensions.preferredExt co_alpha co_att E"
      using preferred_extensions_exist by blast
    have "extensions.completeExt co_alpha co_att E"
      using pref unfolding extensions.preferredExt_def maximal_rel_def by blast
    then show False
      using sh pref unfolding shared_conclusion_def proximal_explanation_def
      by (auto simp: co_alpha_complete)
  qed
  have b: "\<not> shared_conclusion co_beta co_att co_con True"
  proof
    assume sh: "shared_conclusion co_beta co_att co_con True"
    obtain E where pref: "extensions.preferredExt co_beta co_att E"
      using preferred_extensions_exist by blast
    have "extensions.completeExt co_beta co_att E"
      using pref unfolding extensions.preferredExt_def maximal_rel_def by blast
    then show False
      using sh pref unfolding shared_conclusion_def proximal_explanation_def
      by (auto simp: co_beta_complete)
  qed
  show ?thesis using a b by blast
qed

lemma co_complete:
  "extensions.completeExt (\<lambda>_. True) co_att E \<longleftrightarrow>
    (E \<approx> (\<lambda>_. False)) \<or> E \<approx> co_left \<or> E \<approx> co_right"
  unfolding extensions.completeExt_def extensions.admissibleExt_def
    extensions.conflictfreeExt_def defends_rel_def co_att_def
  by (auto simp: co_all co_ex; blast)

lemma co_left_preferred: "extensions.preferredExt (\<lambda>_. True) co_att co_left"
  unfolding extensions.preferredExt_def maximal_rel_def co_complete id_def
  by (auto simp: co_all)

lemma co_right_preferred: "extensions.preferredExt (\<lambda>_. True) co_att co_right"
  unfolding extensions.preferredExt_def maximal_rel_def co_complete id_def
  by (auto simp: co_all)

lemma co_preferred:
  "extensions.preferredExt (\<lambda>_. True) co_att E \<longleftrightarrow>
    E \<approx> co_left \<or> E \<approx> co_right"
proof
  assume pref: "extensions.preferredExt (\<lambda>_. True) co_att E"
  have comp: "extensions.completeExt (\<lambda>_. True) co_att E"
    using pref unfolding extensions.preferredExt_def maximal_rel_def by blast
  have left_comp: "extensions.completeExt (\<lambda>_. True) co_att co_left"
    using co_left_preferred unfolding extensions.preferredExt_def maximal_rel_def by blast
  have nonempty: "\<not> E \<approx> (\<lambda>_. False)"
  proof
    assume empty: "E \<approx> (\<lambda>_. False)"
    have sub: "E \<subseteq> co_left" using empty by blast
    have "co_left \<approx> E"
      using pref left_comp sub
      unfolding extensions.preferredExt_def maximal_rel_def id_def by blast
    then show False using empty by (auto simp: co_all)
  qed
  show "E \<approx> co_left \<or> E \<approx> co_right"
    using comp nonempty by (auto simp: co_complete)
next
  assume "E \<approx> co_left \<or> E \<approx> co_right"
  then have "E = co_left \<or> E = co_right" by (auto simp: fun_eq_iff)
  then show "extensions.preferredExt (\<lambda>_. True) co_att E"
    using co_left_preferred co_right_preferred by auto
qed

lemma co_shared_argument: "shared_argument (\<lambda>_. True) co_att co_con True"
  unfolding shared_argument_def proximal_explanation_def
  by (auto simp: co_preferred co_all co_ex)

lemma co_no_shared_explanation: "\<not> shared_explanation (\<lambda>_. True) co_att co_con True"
proof
  assume strong: "shared_explanation (\<lambda>_. True) co_att co_con True"
  obtain E where expl: "explanation (\<lambda>_. True) co_att co_con True E"
    and shared: "\<forall>P. extensions.preferredExt (\<lambda>_. True) co_att P \<longrightarrow> E \<subseteq> P"
    using strong unfolding shared_explanation_def by blast
  have support: "explanation_support (\<lambda>_. True) co_att co_con True E"
    by (rule explanation_has_support[OF expl])
  have left: "E \<subseteq> co_left"
    using shared[rule_format, OF co_left_preferred] by blast
  have right: "E \<subseteq> co_right"
    using shared[rule_format, OF co_right_preferred] by blast
  have member: "E CA"
    using support unfolding explanation_support_def by (auto simp: co_ex)
  have defended: "defends_rel (\<lambda>_. True) co_att E CA"
    using support member unfolding explanation_support_def by blast
  have no_defender: "\<not> E CG \<and> \<not> E CH"
    using left right by (auto simp: co_all)
  show False using defended no_defender
    unfolding defends_rel_def co_att_def by (auto simp: co_all co_ex)
qed

theorem co_distal_disagreement_only_in_coalition:
  "\<not> shared_conclusion co_alpha co_att co_con True \<and>
    \<not> shared_conclusion co_beta co_att co_con True \<and>
    distal_implicit_disagreement co_alpha co_beta co_att co_con True \<and>
    \<not> potential_distal_disagreement co_alpha co_beta co_att co_con True"
proof -
  have shared: "shared_conclusion (\<lambda>_. True) co_att co_con True"
    by (rule shared_argument_imp_shared_conclusion[OF co_shared_argument])
  have distal: "distal_disagreement (coalition co_alpha co_beta) co_att co_con True"
    unfolding distal_disagreement_def
    by (subst co_coalition_all)+ (use shared co_no_shared_explanation in blast)
  have npot: "\<not> potential_distal_disagreement co_alpha co_beta co_att co_con True"
    using co_agents_reject unfolding potential_distal_disagreement_def by blast
  show ?thesis using co_agents_reject distal npot by blast
qed

end
