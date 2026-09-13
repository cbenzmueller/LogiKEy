theory ID_Inference
  imports ID_Frameworks
begin

section \<open>Inference relations\<close>

text \<open>Proximal explanation (paper's \<^emph>\<open>proximal explanation\<close>). It is a relation,
since several arguments may explain the same conclusion, and does not require the
argument to belong to an extension.\<close>
definition proximal_explanation :: "'a Set \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> bool" where
  "proximal_explanation U Con p a \<longleftrightarrow> U a \<and> Con a = p"

text \<open>Inference relations (paper's Inference-relations definition). The U guard is
essential: the imported relative semantics allow arbitrary predicate values outside
the argument universe. The first two
relations quantify extension then argument; the third uses a single argument
across all preferred extensions. No finite enumeration of extensions is assumed.\<close>
definition credulous_conclusion :: "'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> bool" where
  "credulous_conclusion U att Con p \<longleftrightarrow>
    (\<exists>E. extensions.preferredExt U att E \<and>
      (\<exists>a. E a \<and> proximal_explanation U Con p a))"

definition shared_conclusion :: "'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> bool" where
  "shared_conclusion U att Con p \<longleftrightarrow>
    (\<forall>E. extensions.preferredExt U att E \<longrightarrow>
      (\<exists>a. E a \<and> proximal_explanation U Con p a))"

definition shared_argument :: "'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> bool" where
  "shared_argument U att Con p \<longleftrightarrow>
    (\<exists>a. proximal_explanation U Con p a \<and>
      (\<forall>E. extensions.preferredExt U att E \<longrightarrow> E a))"

text \<open>The ``agrees that'' and ``agrees because'' definitions introduce names for
existing inference relations.\<close>
abbreviation agrees_that where "agrees_that \<equiv> shared_conclusion"
abbreviation agrees_because where "agrees_because \<equiv> shared_argument"

lemma shared_argument_imp_shared_conclusion:
  "shared_argument U att Con p \<Longrightarrow> shared_conclusion U att Con p"
  unfolding shared_argument_def shared_conclusion_def by blast

lemma shared_conclusion_imp_credulous:
  "shared_conclusion U att Con p \<Longrightarrow> credulous_conclusion U att Con p"
  using preferred_extensions_exist[of U att]
  unfolding shared_conclusion_def credulous_conclusion_def by blast

lemma conclusion_inference_induced [simp]:
  "credulous_conclusion U (induced_att att U) Con p = credulous_conclusion U att Con p"
  "shared_conclusion U (induced_att att U) Con p = shared_conclusion U att Con p"
  "shared_argument U (induced_att att U) Con p = shared_argument U att Con p"
  unfolding credulous_conclusion_def shared_conclusion_def shared_argument_def by simp_all

lemma no_argument_no_credulous:
  "(\<forall>a. U a \<longrightarrow> Con a \<noteq> p) \<Longrightarrow> \<not> credulous_conclusion U att Con p"
  unfolding credulous_conclusion_def proximal_explanation_def by blast

lemma empty_framework_no_conclusion:
  "\<not> credulous_conclusion (\<lambda>_. False) att Con p \<and>
   \<not> shared_conclusion (\<lambda>_. False) att Con p \<and>
   \<not> shared_argument (\<lambda>_. False) att Con p"
  by (metis no_argument_no_credulous shared_argument_imp_shared_conclusion
      shared_conclusion_imp_credulous)

end
