theory IO_LogicalBase
  imports Main
begin

(*----------- Technicalities --------*)
(* declare[[smt_timeout=30]] *)
(* declare[[show_types]] *)
(* declare[[syntax_ambiguity_warning=false]] *)
(* sledgehammer_params[isar_proof=false] *)
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2, timeout=120]

typedecl i

type_synonym \<tau> = "i \<Rightarrow> bool"

consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)

definition setnot   :: "\<tau> \<Rightarrow> \<tau>" ("\<^bold>\<not>_" [52] 53)
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not> \<phi> w"

definition setor    :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>" (infixr "\<^bold>\<or>" 50)
  where "\<phi> \<^bold>\<or> \<psi> \<equiv> \<lambda>w. \<phi> w \<or> \<psi> w"

definition setand   :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>" (infixr "\<^bold>\<and>" 51)
  where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<lambda>w. \<phi> w \<and> \<psi> w"

definition setimp   :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>" (infixr "\<^bold>\<longrightarrow>" 49)
  where "\<phi> \<^bold>\<longrightarrow> \<psi> \<equiv> \<lambda>w. \<phi> w \<longrightarrow> \<psi> w"

definition setcoimp :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>" (infixr "\<^bold>\<hookleftarrow>" 52)
  where "\<phi> \<^bold>\<hookleftarrow> \<psi> \<equiv> \<lambda>w. \<phi> w \<and> \<not> \<psi> w"

definition setbox   :: "\<tau> \<Rightarrow> \<tau>" ("\<^bold>\<box>\<^sub>k")
  where "\<^bold>\<box>\<^sub>k \<phi> \<equiv> \<lambda>w. \<forall>v. w r v \<longrightarrow> \<phi> v"

definition settrue  :: "\<tau>" ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<lambda>w. True"

definition setfalse :: "\<tau>" ("\<^bold>\<bottom>")
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"

definition setvalid :: "\<tau> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>" [8] 109)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"

abbreviation (input) msubset :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> bool" (infix "\<^bold>\<le>" 53)
  where "\<phi> \<^bold>\<le> \<psi> \<equiv> \<forall>w. \<phi> w \<longrightarrow> \<psi> w"

(* Pointwise order on unary operators. *)
abbreviation (input) msubsetrelation :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> (\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool" (infix "\<^bold>\<subseteq>" 54)
  where "op1 \<^bold>\<subseteq> op2 \<equiv> \<forall>\<phi>. op1 \<phi> \<^bold>\<le> op2 \<phi>"

lemma ANDtoORDER: "(\<phi> \<^bold>\<and> \<psi>) = \<phi> \<longrightarrow> (\<phi> \<^bold>\<le> \<psi>)"
  by (metis setand_def)

lemma ORtoORDER: "(\<phi> \<^bold>\<or> \<psi>) = \<psi> \<longrightarrow> (\<phi> \<^bold>\<le> \<psi>)"
  by (metis setor_def)

lemma ORDERtoAND: "(\<phi> \<^bold>\<le> \<psi>) \<longrightarrow> (\<phi> \<^bold>\<and> \<psi>) = \<phi>"
  by (auto simp: setand_def)

lemma ORDERtoOR: "(\<phi> \<^bold>\<le> \<psi>) \<longrightarrow> (\<phi> \<^bold>\<or> \<psi>) = \<psi>"
  by (auto simp: setor_def)

lemma coimplication1:
  "((\<phi> \<^bold>\<hookleftarrow> \<psi>) \<^bold>\<le> \<chi>) \<longrightarrow> (\<phi> \<^bold>\<le> (\<psi> \<^bold>\<or> \<chi>))"
  by (auto simp: setcoimp_def setor_def)

lemma coimplication2:
  "(\<phi> \<^bold>\<le> (\<psi> \<^bold>\<or> \<chi>)) \<longrightarrow> ((\<phi> \<^bold>\<hookleftarrow> \<psi>) \<^bold>\<le> \<chi>)"
  by (metis setcoimp_def setor_def)

definition monotone :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where "monotone op \<equiv> \<forall>\<phi> \<psi>. (\<phi> \<^bold>\<le> \<psi>) \<longrightarrow> (op \<phi> \<^bold>\<le> op \<psi>)"

definition regular_dia :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where "regular_dia op \<equiv> \<forall>\<phi> \<psi>. op (\<phi> \<^bold>\<or> \<psi>) = (op \<phi> \<^bold>\<or> op \<psi>)"

definition normal_dia :: "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> bool"
  where "normal_dia op \<equiv> regular_dia op \<and> op \<^bold>\<bottom> = \<^bold>\<bottom>"

definition infimum :: "(\<tau> \<Rightarrow> bool) \<Rightarrow> \<tau>" ("\<^bold>\<And>_")
  where "\<^bold>\<And>S \<equiv> \<lambda>w. \<forall>X. S X \<longrightarrow> X w"

lemma infimum_member:
  assumes "S X"
  shows "\<^bold>\<And>S \<^bold>\<le> X"
  using assms by (auto simp: infimum_def)

lemma infimum_greatest:
  assumes "\<forall>X. S X \<longrightarrow> Y \<^bold>\<le> X"
  shows "Y \<^bold>\<le> \<^bold>\<And>S"
  using assms by (auto simp: infimum_def)

lemma infimum_empty [simp]: "\<^bold>\<And>(\<lambda>x. False) = (\<lambda>w. True)"
  by (simp add: infimum_def)

lemma infimum_UNIV [simp]: "\<^bold>\<And>(\<lambda>x. True) = (\<lambda>w. False)"
  by (auto simp: infimum_def)

lemma infimum_singleton [simp]: "\<^bold>\<And>(\<lambda>x. x = X) = X"
  by (auto simp: infimum_def)

lemma and_top_infimum_empty [simp]: "\<phi> \<^bold>\<and> \<^bold>\<And>(\<lambda>x. False) = \<phi>"
  by (simp add: infimum_def ORDERtoAND)

(* Consequence-closure and consistency for families of formulas, represented
   explicitly as predicates \<tau> \<Rightarrow> bool. *)
definition Cn :: "(\<tau> \<Rightarrow> bool) \<Rightarrow> \<tau> \<Rightarrow> bool"
  where "Cn A \<equiv> \<lambda>\<phi>. (\<^bold>\<And>A) \<^bold>\<le> \<phi>"

definition fconsistent :: "(\<tau> \<Rightarrow> bool) \<Rightarrow> bool"
  where "fconsistent A \<equiv> (\<^bold>\<And>A) \<noteq> \<^bold>\<bottom>"

lemma CnI:
  assumes "(\<^bold>\<And>A) \<^bold>\<le> \<phi>"
  shows "Cn A \<phi>"
  using assms unfolding Cn_def by simp

lemma CnD:
  assumes "Cn A \<phi>"
  shows "(\<^bold>\<And>A) \<^bold>\<le> \<phi>"
  using assms unfolding Cn_def by simp

lemma Cn_extensive:
  assumes "A \<phi>"
  shows "Cn A \<phi>"
  using assms infimum_member unfolding Cn_def by blast

(*----------- shared I/O-logic layer --------*)

consts IO :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> bool" (infixr "\<^bold>\<preceq>" 70)

definition slanted :: "\<tau> \<Rightarrow> \<tau>" ("\<^bold>\<diamond>")
  where "\<^bold>\<diamond> \<phi> \<equiv> \<^bold>\<And>(\<lambda>x. \<phi> \<^bold>\<preceq> x)"

(* Optional relational background notions from the paper.  The Applications-style
   theories below do not need them as axioms, but they are useful to have in the
   common base. *)
definition DD :: "(\<tau> \<Rightarrow> \<tau> \<Rightarrow> bool) \<Rightarrow> bool"
  where "DD R \<equiv> \<forall>a x1 x2. R a x1 \<and> R a x2 \<longrightarrow> (\<exists>x. R a x \<and> x \<^bold>\<le> x1 \<and> x \<^bold>\<le> x2)"

definition SF :: "(\<tau> \<Rightarrow> \<tau> \<Rightarrow> bool) \<Rightarrow> bool"
  where "SF R \<equiv> \<forall>x. \<exists>y. R x y"

lemma regular_dia_implies_mono:
  "regular_dia op \<longrightarrow> monotone op"
  unfolding regular_dia_def monotone_def
  by (metis ORDERtoOR setor_def)

lemma slanted_from_norm:
  assumes "\<alpha> \<^bold>\<preceq> \<beta>"
  shows "(\<^bold>\<diamond> \<alpha>) \<^bold>\<le> \<beta>"
  using assms by (metis infimum_member slanted_def)

lemma dominated_by_slanted_from_norm:
  assumes dom: "\<forall>\<phi>. op \<phi> \<^bold>\<le> (\<^bold>\<diamond> \<phi>)"
  assumes rel: "\<alpha> \<^bold>\<preceq> \<beta>"
  shows "op \<alpha> \<^bold>\<le> \<beta>"
  using dom[rule_format, of \<alpha>] slanted_from_norm[OF rel] by auto

end
