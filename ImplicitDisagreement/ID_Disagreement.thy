theory ID_Disagreement
  imports ID_Explanations
begin

text \<open>Disagreement predicates (paper Definition ``Disagreements, explicit and
implicit''); the proximal/distal naming matches the paper. Each predicate is the
characteristic predicate of the corresponding conclusion set (Dis, proximal,
distal); evaluate it on the coalition argument predicate for the two-agent
formulation.\<close>
definition disagrees_that where
  "disagrees_that U att Con p \<longleftrightarrow>
    credulous_conclusion U att Con p \<and> \<not> shared_conclusion U att Con p"

definition proximal_disagreement where
  "proximal_disagreement U att Con p \<longleftrightarrow>
    shared_conclusion U att Con p \<and> \<not> shared_argument U att Con p"

definition distal_disagreement where
  "distal_disagreement U att Con p \<longleftrightarrow>
    shared_conclusion U att Con p \<and> \<not> shared_explanation U att Con p"

text \<open>Actual implicit disagreement coincides with the proximal/distal
disagreement predicates above, evaluated on the coalition. Potential disagreement
keeps A and B as separate parameters: its truth cannot be determined from their
union alone.\<close>
abbreviation proximal_implicit_disagreement where
  "proximal_implicit_disagreement A B att Con p \<equiv>
    proximal_disagreement (coalition A B) att Con p"

abbreviation distal_implicit_disagreement where
  "distal_implicit_disagreement A B att Con p \<equiv>
    distal_disagreement (coalition A B) att Con p"

definition potential_proximal_disagreement where
  "potential_proximal_disagreement A B att Con p \<longleftrightarrow>
    shared_conclusion A att Con p \<and> shared_conclusion B att Con p \<and>
    \<not> shared_argument (coalition A B) att Con p"

definition potential_distal_disagreement where
  "potential_distal_disagreement A B att Con p \<longleftrightarrow>
    shared_conclusion A att Con p \<and> shared_conclusion B att Con p \<and>
    \<not> shared_explanation (coalition A B) att Con p"

text \<open>Weak spots (paper Definition ``weak spot''). Losing skeptical acceptance
alone is insufficient: after removal, the conclusion must still be credulously
supported. Pass coalition A B for U to obtain a weak spot of that coalition.\<close>
definition weak_spot where
  "weak_spot U att Con p a \<longleftrightarrow>
    shared_conclusion U att Con p \<and>
    disagrees_that (remove_argument U a) (remove_att U att a) Con p"

text \<open>The unnumbered antagonist notion on p. 8 is made precise by the
following explicit convention: removing a present argument turns distal disagreement
into agreement from a shared explanation. This is a modelling choice for the
informal passage, not an additional numbered definition in the paper.\<close>
definition antagonist where
  "antagonist U att Con p a \<longleftrightarrow>
    U a \<and> distal_disagreement U att Con p \<and>
    shared_explanation (remove_argument U a) (remove_att U att a) Con p"

lemma proximal_imp_distal:
  "proximal_disagreement U att Con p \<Longrightarrow> distal_disagreement U att Con p"
  using shared_explanation_imp_shared_argument[of U att Con p]
  unfolding proximal_disagreement_def distal_disagreement_def by blast

lemma potential_proximal_imp_distal:
  "potential_proximal_disagreement A B att Con p \<Longrightarrow>
    potential_distal_disagreement A B att Con p"
  using shared_explanation_imp_shared_argument[of "coalition A B" att Con p]
  unfolding potential_proximal_disagreement_def potential_distal_disagreement_def by blast

text \<open>Ordinary disagreement is disjoint from both proximal and distal
disagreement, as follows from their definitions.\<close>
lemma ordinary_and_distal_disjoint:
  "\<not> (disagrees_that U att Con p \<and> distal_disagreement U att Con p)"
  unfolding disagrees_that_def distal_disagreement_def by blast

lemma ordinary_and_proximal_disjoint:
  "\<not> (disagrees_that U att Con p \<and> proximal_disagreement U att Con p)"
  unfolding disagrees_that_def proximal_disagreement_def by blast

lemma weak_spot_retains_credulous_support:
  "weak_spot U att Con p a \<Longrightarrow>
    credulous_conclusion (remove_argument U a) att Con p \<and>
    \<not> shared_conclusion (remove_argument U a) att Con p"
  unfolding weak_spot_def disagrees_that_def by simp

lemma weak_spot_is_present:
  assumes "weak_spot U att Con p a"
  shows "U a" 
proof (rule ccontr)
  assume absent: "\<not> U a"
  have unchanged: "remove_argument U a = U"
    using absent by (auto simp: fun_eq_iff)
  show False
    using assms unfolding weak_spot_def disagrees_that_def
    by (auto simp: unchanged)
qed

lemma removing_the_only_concluder_is_not_a_weak_spot:
  assumes "\<forall>b. U b \<longrightarrow> Con b = p \<longrightarrow> b = a"
  shows "\<not> weak_spot U att Con p a" 
  by (smt (verit, ccfv_threshold) assms no_argument_no_credulous weak_spot_retains_credulous_support)


lemma antagonists_are_not_weak_spots:
  assumes ant: "antagonist U att Con p a"
  shows "\<not> weak_spot U att Con p a" 
  by (metis (lifting) agreement_hierarchy antagonist_def assms disagrees_that_def weak_spot_def)

end
