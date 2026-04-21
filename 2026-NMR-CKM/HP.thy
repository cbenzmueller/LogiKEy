(* Luca Pasetto, Roberts Tarvids, Apostolos Tzimoulis and Christoph Benzmüller, 2026 *)
theory HP
  imports Main Helper
begin

text ‹Shallow embedding of single-world causal models in HOL.›

text ‹Type declarations›
typedecl 𝗏  (* Causal variables *)
typedecl ι  (* Individuals *)

type_synonym 𝒳 = "𝗏 ⇒ bool"              (* Sets of causal variables *)
type_synonym ℛ = "𝗏 ⇒ (ι ⇒ bool)" (* Ranges of variables *)
type_synonym 𝖿 = "(𝗏 ⇒ ι) ⇒ ι" (* Structural equations *)
type_synonym ℱ = "𝗏 ⇒ 𝖿"               (* Families of structural equations *)
type_synonym 𝗍 = "𝗏 ⇒ ι"             (* Total assignments / contexts *)

type_synonym Φ   = "ℱ ⇒ bool"

consts
  U  :: 𝒳    (* Exogenous variables *)
  V  :: 𝒳    (* Endogenous variables *)
  F  :: ℱ    (* Initial structural family *)
  R  :: ℛ    (* Ranges *)
  tx :: 𝗍    (* Actual exogenous context *)

abbreviation (input) directly_depends :: "𝗏 ⇒ 𝖿 ⇒ 𝒳" where
  "directly_depends y f ≡
     λx. ∃i1 i2 Z. x ≠ y ∧ i1 ≠ i2 ∧ R x i1 ∧ R x i2 ∧
          f (fun_upd Z x i1) ≠ f (fun_upd Z x i2)"

definition directly_causes :: "ℱ ⇒ (𝗏 ⇒ 𝗏 ⇒ bool)" where
  "directly_causes G ≡ λx v. directly_depends v (G v) x"

axiomatization where
  disjoint_variables: "∀x. U x ⟷ ¬ V x" and
  exo: "∀x a. U x ⟶ F x a = tx x" and
  equations_respect_ranges: "∀v t. R v (F v t)" and
  tx_respects_F: "∀v. F v tx = tx v" and
  depends_only_on_direct_causes:
    "∀v a1 a2. (∀x. directly_depends v (F v) x ⟶ a1 x = a2 x) ⟶ F v a1 = F v a2"

lemma tx_respects_ranges: "∀v. R v (tx v)"
  by (metis equations_respect_ranges tx_respects_F)

lemma nonempty_ranges: "∀v. ∃i. R v i"
  using tx_respects_ranges by auto

lemma no_self_dependence:
  "∀v a1 a2. (∀w. w ≠ v ⟶ a1 w = a2 w) ⟶ F v a1 = F v a2"
  using depends_only_on_direct_causes by blast

lemma exo_no_direct_dep: "∀x v. U v ⟶ ¬ directly_depends v (F v) x"
  by (simp add: exo)

text ‹Fixed-point view of solutions.›
definition next_ctx :: "ℱ ⇒ 𝗍 ⇒ 𝗍" where
  "next_ctx G ctx ≡ (λv. if U v then tx v else G v ctx)"

definition Fix :: "ℱ ⇒ 𝗍 ⇒ bool" where
  "Fix G ctx ≡ next_ctx G ctx = ctx"

lemma Fix_iff_solution:
  "Fix G ctx ⟷
     (∀u. U u ⟶ ctx u = tx u) ∧ (∀v. V v ⟶ ctx v = G v ctx)"
  by (metis (lifting) Fix_def disjoint_variables ext next_ctx_def)

text ‹A fixed topological order for the initial family F.›
consts ord :: "𝗏 list"

axiomatization where
  ord_distinct: "distinct ord" and
  ord_complete: "set ord = {v. V v}" and
  topo_ord: "directly_causes F x v ⟹ U x ∨ find_index ord x < find_index ord v"

lemma recur_ord:
  "∀x v. x ≠ v ⟶
      ((U x ∧ V v) ∨ (V x ∧ V v ∧ find_index ord x < find_index ord v)) ⟶
      ¬ ((U v ∧ V x) ∨ (V v ∧ V x ∧ find_index ord v < find_index ord x))"
  by (metis disjoint_variables less_irrefl less_trans)

definition step_ctx :: "ℱ ⇒ 𝗍 ⇒ 𝗏 ⇒ 𝗍" where
  "step_ctx G c v ≡ fun_upd c v (G v c)"

definition cv :: "ℱ ⇒ 𝗍" where
  "cv G ≡ foldl (step_ctx G) tx ord"

lemma foldl_step_notin:
  assumes "x ∉ set xs"
  shows "foldl (step_ctx G) c xs x = c x"
  using assms
proof (induction xs arbitrary: c)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  have "x ≠ a" and "x ∉ set xs" using Cons.prems by auto
  then show ?case using Cons.IH step_ctx_def by force
qed

lemma cv_exo [simp]:
  assumes "U u"
  shows "cv G u = tx u"
  using assms cv_def disjoint_variables foldl_step_notin ord_complete by force

lemma index_at_split [simp]:
  assumes dist: "distinct (prefix @ v # suffix)"
  shows "find_index (prefix @ v # suffix) v = length prefix"
  by (metis add_less_cancel_left append.right_neutral dist distinct_Ex1 find_index_lt_length_if_mem 
         find_index_nth_if_mem length_Cons length_append list.size(3) nth_append_length nth_mem zero_less_Suc)

text ‹Language›

definition AtomPhi :: "𝗏 ⇒ ι ⇒ Φ" ("_=⇧h⇧p⇧p_") where
  "v =⇧h⇧p⇧p i ≡ λG. V v ∧ R v i ∧ cv G v = i"

definition NegationPhi :: "Φ ⇒ Φ" ("¬⇧h⇧p⇧p") where
  "¬⇧h⇧p⇧p φ ≡ λG. ¬ φ G"

definition ConjunctionPhi :: "Φ ⇒ Φ ⇒ Φ" (infixr "∧⇧h⇧p⇧p" 95) where
  "φ ∧⇧h⇧p⇧p ψ ≡ λG. φ G ∧ ψ G"

definition ImplicationPhi :: "Φ ⇒ Φ ⇒ Φ" (infixr "→⇧h⇧p⇧p" 95) where
  "φ →⇧h⇧p⇧p ψ ≡ λG. φ G ⟶ ψ G"

definition wf_intervention :: "𝗏 ⇒ ι ⇒ bool" where
  "wf_intervention v i ≡ V v ∧ R v i"

lemma wf_intervention_iff [simp]: "wf_intervention v i ⟷ V v ∧ R v i"
  unfolding wf_intervention_def by simp

definition update_F :: "ℱ ⇒ 𝒳 ⇒ (𝗏 ⇒ ι) ⇒ ℱ" where
  "update_F G Y b ≡ λv a. if Y v ∧ wf_intervention v (b v) then b v else G v a"

definition Intervention :: "𝒳 ⇒ (𝗏 ⇒ ι) ⇒ Φ ⇒ Φ" ("[_←_]_") where
  "[Y ← b] φ ≡ λG. φ (update_F G Y b)"

inductive reachable :: "ℱ ⇒ bool" where
  reachable_base [intro]: "reachable F" |
  reachable_step [intro]: "reachable G ⟹ reachable (update_F G Y b)"

lemma directly_causes_update_subset [simp]:
  assumes "directly_causes (update_F G Y b) x v"
  shows "directly_causes G x v"
  using assms unfolding directly_causes_def update_F_def by metis

definition Truth :: "ℱ ⇒ Φ ⇒ bool" ("⟨_⟩ ⊨⇧h⇧p⇧p _") where
  "⟨G⟩ ⊨⇧h⇧p⇧p φ ≡ φ G"

definition Validity ("⊨⇧h⇧p⇧p _") where
  "⊨⇧h⇧p⇧p φ ≡ ∀G. reachable G ⟶ ⟨G⟩ ⊨⇧h⇧p⇧p φ"

lemma reachable_update_F [intro]: "reachable (update_F F Y b)"
  by (rule reachable_step[OF reachable_base])

lemma reachable_directly_causes_subset_F [simp]:
  assumes "reachable G" and "directly_causes G x v"
  shows "directly_causes F x v"
  using assms by induction auto

lemma reachable_respects_ranges [simp]:
  assumes "reachable G"
  shows "∀v t. R v (G v t)"
  using assms by (induction) (auto simp: equations_respect_ranges update_F_def)

lemma reachable_exo [simp]:
  assumes "reachable G"
  shows "∀x a. U x ⟶ G x a = tx x"
  using assms by (induction) (auto simp: exo update_F_def disjoint_variables)

lemma reachable_locality [simp]:
  assumes "reachable G"
  shows "∀v a1 a2. (∀x. directly_depends v (G v) x ⟶ a1 x = a2 x) ⟶ G v a1 = G v a2"
  using assms
  apply induction
  using depends_only_on_direct_causes apply blast
  by (smt (verit, del_insts) update_F_def)

lemma reachable_topo_index [simp]:
  assumes "reachable G" and "directly_causes G x v"
  shows "U x ∨ find_index ord x < find_index ord v"
  by (metis assms reachable_directly_causes_subset_F topo_ord)

lemma cv_reachable_endo [simp]:
  assumes rG: "reachable G" and Vv: "V v"
  shows "cv G v = G v (cv G)"
proof -
  from ord_complete Vv have vmem: "v ∈ set ord" by auto
  then obtain prefix suffix where dec: "ord = prefix @ v # suffix"
    using split_list by metis
  let ?cpre = "foldl (step_ctx G) tx prefix"
  have dist: "distinct (prefix @ v # suffix)" using ord_distinct dec by simp
  have vnot: "v ∉ set suffix" using dist by auto
  have cvv: "cv G v = G v ?cpre"
    using foldl_step_notin[OF vnot]
    by (simp add: cv_def dec step_ctx_def)
  have agree: "∀x. directly_depends v (G v) x ⟶ ?cpre x = cv G x"
  proof (intro allI impI)
    fix x
    assume dx: "directly_depends v (G v) x"
    have topo: "U x ∨ find_index ord x < find_index ord v"
      using reachable_topo_index[OF rG] dx unfolding directly_causes_def by blast
    show "?cpre x = cv G x"
    proof (cases "U x")
      case True
      have xnotpref: "x ∉ set prefix"
        using True ord_complete disjoint_variables dec
        by (metis append_eq_conv_conj in_set_takeD mem_Collect_eq)
      then show ?thesis
        by (simp add: foldl_step_notin True)
    next
      case False
      then have Vx: "V x" using disjoint_variables by blast
      have xmem: "x ∈ set ord" using ord_complete Vx by auto
      have idx: "find_index ord x < find_index ord v" using topo False by simp
      have idxv: "find_index ord v = length prefix"
        unfolding dec by (rule index_at_split[OF dist])
      have idx_lt_pref: "find_index ord x < length prefix" using idx idxv by simp
      have xpref: "x ∈ set prefix"
        using find_index_nth_if_mem[OF xmem] idx_lt_pref
        by (metis nth_mem nth_append_left dec)
      have xnot: "x ∉ set (v # suffix)" using xpref dist by auto
      have "cv G x = foldl (step_ctx G) (step_ctx G ?cpre v) suffix x"
        unfolding cv_def dec by simp
      also have "... = ?cpre x"
        using foldl_step_notin xnot by (simp add: step_ctx_def)
      finally show ?thesis by simp
    qed
  qed
  show ?thesis
    using cvv reachable_locality[OF rG] agree by (metis (lifting) ext)
qed

lemma cv_reachable_fix [simp]:
  assumes "reachable G"
  shows "Fix G (cv G)"
  using Fix_iff_solution cv_exo cv_reachable_endo assms by blast

lemma fix_agree_endo [simp]:
  assumes rG: "reachable G" and fix1: "Fix G c1" and fix2: "Fix G c2" and Vv: "V v"
  shows "c1 v = c2 v"
  using Vv
proof (induction v rule: measure_induct_rule[of "λv. find_index ord v"])
  case (less v)
  have c1v: "c1 v = G v c1" using fix1 less.prems unfolding Fix_iff_solution by blast
  have c2v: "c2 v = G v c2" using fix2 less.prems unfolding Fix_iff_solution by blast
  have agree: "∀x. directly_depends v (G v) x ⟶ c1 x = c2 x"
  proof (intro allI impI)
    fix x
    assume dx: "directly_depends v (G v) x"
    have topo: "U x ∨ find_index ord x < find_index ord v"
      using reachable_topo_index[OF rG] dx unfolding directly_causes_def by blast
    show "c1 x = c2 x"
    proof (cases "U x")
      case True
      then show ?thesis
        using fix1 fix2 unfolding Fix_iff_solution by simp
    next
      case False
      then show ?thesis
        using less.IH[of x] topo disjoint_variables by blast
    qed
  qed
  show ?case
    using c1v c2v reachable_locality[OF rG] agree by (smt (verit, best))
qed

lemma fix_unique [simp]:
  assumes "reachable G" and "Fix G c1" and "Fix G c2"
  shows "c1 = c2"
  using assms unfolding Fix_iff_solution 
  by (metis (no_types, opaque_lifting) assms disjoint_variables ext fix_agree_endo)

lemma reachable_unique_solution [simp]:
  assumes "reachable G"
  shows "∃!ctx. Fix G ctx"
  by (metis cv_reachable_fix fix_unique assms)

lemma cv_eq_if_fix [simp]:
  assumes "reachable G" and "Fix G c"
  shows "cv G = c"
  using assms by fastforce

lemma cv_intervention_hit [simp]:
  assumes rG: "reachable G" and Yv: "Y v" and Vv: "V v" and Rv: "R v (b v)"
  shows "cv (update_F G Y b) v = b v"
  by (metis Rv Vv Yv cv_reachable_endo rG reachable_step update_F_def wf_intervention_iff)

lemma cv_update_range [simp]:
  assumes "V v"
  shows "R v (cv (update_F F Y b) v)"
  by (metis assms cv_reachable_endo reachable_respects_ranges reachable.simps)

lemma fix_strengthen_intervention [simp]:
  assumes "Fix (update_F F Y b) c" and "V v1" and "R v1 i1" and "c v1 = i1"
  shows "Fix (update_F F (fun_upd Y v1 True) (fun_upd b v1 i1)) c"
  using Fix_iff_solution assms update_F_def by fastforce

lemma directly_depends_const [simp]:
  "¬ directly_depends v (λ_. (c :: ι)) x"
  by simp

end
