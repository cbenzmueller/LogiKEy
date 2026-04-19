(* Luca Pasetto, Roberts Tarvids, Apostolos Tzimoulis and Christoph Benzmüller, 2026 *)
theory CKM
  imports Main Helper
begin

text ‹Shallow embedding of causal Kripke models in HOL.›

text ‹Type declarations›
typedecl 𝗏    (* Causal variables *)
typedecl ι    (* Individuals *)
typedecl 𝗐    (* Possible worlds *)

type_synonym 𝒳 = "𝗏 ⇒ bool"                    (* Sets of causal variables *)
type_synonym 𝒲 = "𝗐 ⇒ bool"                (* Set of worlds in the model *)
type_synonym 𝒜 = "𝗐 ⇒ 𝗐 ⇒ bool"           (* Accessibility relation *)
type_synonym 𝒴 = "𝗐 ⇒ 𝗏 ⇒ bool"          (* Sets of world / variable pairs *)
type_synonym ℛ = "𝗐 ⇒ 𝗏 ⇒ ι ⇒ bool"     (* World-sensitive ranges *)
type_synonym 𝗍 = "𝗐 ⇒ 𝗏 ⇒ ι"             (* Total assignments / contexts *)
type_synonym 𝖿 = "𝗍 ⇒ ι"                  (* Structural equations *)
type_synonym ℱ = "𝗐 ⇒ 𝗏 ⇒ 𝖿"            (* Structural families *)

type_synonym Φ = "𝗐 ⇒ ℱ ⇒ bool"

consts
  U  :: 𝒳      (* Exogenous variables *)
  V  :: 𝒳      (* Endogenous variables *)
  W  :: 𝒲   (* Worlds in the Kripke model *)
  A  :: 𝒜      (* Accessibility relation *)
  F  :: ℱ      (* Distinguished structural family *)
  R  :: ℛ      (* World-sensitive ranges *)
  tx :: 𝗍      (* Actual exogenous context *)

definition Uw :: "𝗐 ⇒ 𝗏 ⇒ bool" where
  "Uw w x ⟷ W w ∧ U x"

definition Vw :: "𝗐 ⇒ 𝗏 ⇒ bool" where
  "Vw w x ⟷ W w ∧ V x"

text ‹
  (y,w') directly depends on (x,w) if changing the value of (x,w) while keeping the
  rest of the assignment fixed can change the value produced by the equation for (y,w').
  The forbidden self-case is the exact same world / variable pair, not just the same variable
  at a different world.
›
abbreviation (input) directly_depends :: "𝗐 ⇒ 𝗏 ⇒ 𝖿 ⇒ 𝗐 ⇒ 𝗏 ⇒ bool" where
  "directly_depends w' y f ≡
     λw x. W w ∧ W w' ∧ (w, x) ≠ (w', y) ∧
       (∃i1 i2 Z. i1 ≠ i2 ∧ R w x i1 ∧ R w x i2 ∧
          f (fun_upd2 Z w x i1) ≠ f (fun_upd2 Z w x i2))"

definition directly_causes :: "ℱ ⇒ (𝗐 ⇒ 𝗏 ⇒ 𝗐 ⇒ 𝗏 ⇒ bool)" where
  "directly_causes G ≡ λw x w1 v. directly_depends w1 v (G w1 v) w x"

axiomatization where
  disjoint_variables: "∀x. U x ⟷ ¬ V x" and
  exo: "∀w x a. Uw w x ⟶ F w x a = tx w x" and
  equations_respect_ranges: "∀w v t. R w v (F w v t)" and
  tx_respects_F: "∀w v. F w v tx = tx w v" and
  depends_only_on_direct_causes:
    "∀w v a1 a2.
       (∀w1 x. directly_depends w v (F w v) w1 x ⟶ a1 w1 x = a2 w1 x) ⟶
       F w v a1 = F w v a2" and
  accessibility_closed: "∀w w'. A w w' ⟶ W w ∧ W w'"

lemma Uw_not_Vw [simp]:
  "Uw w x ⟹ ¬ Vw w x"
  unfolding Uw_def Vw_def using disjoint_variables by blast

lemma Vw_not_Uw [simp]:
  "Vw w x ⟹ ¬ Uw w x"
  unfolding Uw_def Vw_def using disjoint_variables by blast

lemma W_imp_Uw_or_Vw:
  "W w ⟹ Uw w x ∨ Vw w x"
  unfolding Uw_def Vw_def using disjoint_variables by blast

lemma tx_respects_ranges:
  "∀w v. R w v (tx w v)"
  by (metis equations_respect_ranges tx_respects_F)

lemma nonempty_ranges:
  "∀w v. ∃i. R w v i"
  using tx_respects_ranges by auto

lemma no_self_dependence:
  "∀w v a1 a2. (∀w1 x. (w1, x) ≠ (w, v) ⟶ a1 w1 x = a2 w1 x) ⟶ F w v a1 = F w v a2"
  using depends_only_on_direct_causes by blast

lemma exo_no_direct_dep:
  "∀w x w1 v. Uw w1 v ⟶ ¬ directly_depends w1 v (F w1 v) w x"
  by (simp add: exo)

text ‹Fixed-point view of solutions. Outside the model, assignments are kept at tx.›
definition next_ctx :: "ℱ ⇒ 𝗍 ⇒ 𝗍" where
  "next_ctx G ctx ≡
     (λw v. if Uw w v then tx w v else if Vw w v then G w v ctx else tx w v)"

definition Fix :: "ℱ ⇒ 𝗍 ⇒ bool" where
  "Fix G ctx ≡ next_ctx G ctx = ctx"

lemma Fix_iff_solution:
  "Fix G ctx ⟷
     (∀w u. Uw w u ⟶ ctx w u = tx w u) ∧
     (∀w v. Vw w v ⟶ ctx w v = G w v ctx) ∧
     (∀w x. ¬ Uw w x ∧ ¬ Vw w x ⟶ ctx w x = tx w x)"
  unfolding Fix_def next_ctx_def 
  apply auto 
     apply (smt (verit, best))
    apply (smt (verit, best) Uw_not_Vw)
   apply (smt (verit, ccfv_threshold))
  by fastforce

text ‹A fixed topological order for the distinguished family F.›
consts ord :: "(𝗐 * 𝗏) list"

axiomatization where
  ord_distinct: "distinct ord" and
  ord_complete: "set ord = {(w, v). Vw w v}" and
  topo_ord:
    "directly_causes F w x w1 v ⟹ Uw w x ∨ find_index ord (w, x) < find_index ord (w1, v)"

text ‹Recursiveness is expressed directly through the fixed order ord.›
lemma recur_ord:
  "∀w x w1 v. (w, x) ≠ (w1, v) ⟶
      ((Uw w x ∧ Vw w1 v) ∨ (Vw w x ∧ Vw w1 v ∧ find_index ord (w, x) < find_index ord (w1, v))) ⟶
      ¬ ((Uw w1 v ∧ Vw w x) ∨ (Vw w1 v ∧ Vw w x ∧ find_index ord (w1, v) < find_index ord (w, x)))"
  using Vw_not_Uw order_less_asym' by blast

text ‹Constructive solver over the fixed order ord.›
definition step_ctx :: "ℱ ⇒ 𝗍 ⇒ 𝗐 ⇒ 𝗏 ⇒ 𝗍" where
  "step_ctx G c w v ≡ fun_upd2 c w v (G w v c)"

definition step_pair :: "ℱ ⇒ 𝗍 ⇒ (𝗐 * 𝗏) ⇒ 𝗍" where
  "step_pair G c p ≡ step_ctx G c (fst p) (snd p)"

definition cv :: "ℱ ⇒ 𝗍" where
  "cv G ≡ foldl (step_pair G) tx ord"

lemma foldl_step_notin:
  assumes "x ∉ set xs"
  shows "foldl (step_pair G) c xs (fst x) (snd x) = c (fst x) (snd x)"
  using assms 
proof (induction xs arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have xa: "x ≠ a" and xxs: "x ∉ set xs"
    using Cons.prems by auto
  have "foldl (step_pair G) c (a # xs) (fst x) (snd x) =
        foldl (step_pair G) (step_pair G c a) xs (fst x) (snd x)"
    by simp
  also have "... = step_pair G c a (fst x) (snd x)"
    using Cons.IH[OF xxs] by simp
  also have "... = c (fst x) (snd x)"
  proof (cases a; cases x)
    fix wa va wx vx
    assume a_def: "a = (wa, va)"
    assume x_def: "x = (wx, vx)"
    from xa have "(wa, va) ≠ (wx, vx)"
      unfolding a_def x_def 
      by blast 
    then show ?thesis
      unfolding a_def x_def step_pair_def step_ctx_def fun_upd2_def by auto
  qed
  finally show ?case .
qed

lemma cv_tx_if_notin_ord [simp]:
  assumes "(w, x) ∉ set ord"
  shows "cv G w x = tx w x"
  unfolding cv_def using foldl_step_notin[of "(w, x)" ord G tx] assms by simp

lemma cv_exo [simp]:
  assumes "Uw w u"
  shows "cv G w u = tx w u"
  using assms ord_complete by auto

lemma cv_outside_model [simp]:
  assumes "¬ Uw w x" "¬ Vw w x"
  shows "cv G w x = tx w x"
  using assms ord_complete by auto

lemma index_at_split [simp]:
  assumes dist: "distinct (prefix @ v # suffix)"
  shows "find_index (prefix @ v # suffix) v = length prefix"
proof -
  have mem: "v ∈ set (prefix @ v # suffix)"
    by simp
  have lt1: "find_index (prefix @ v # suffix) v < length (prefix @ v # suffix)"
    using find_index_lt_length_if_mem[OF mem] .
  have nth1: "(prefix @ v # suffix) ! find_index (prefix @ v # suffix) v = v"
    using find_index_nth_if_mem[OF mem] .
  have lt2: "length prefix < length (prefix @ v # suffix)"
    by simp
  have nth2: "(prefix @ v # suffix) ! length prefix = v"
    by simp
  from dist lt1 lt2 nth1 nth2 show ?thesis
    by (metis distinct_conv_nth)
qed

text ‹Language. We have two kinds of atoms, namely world-indexed atoms and atoms.›
definition AtomPhi :: "𝗐 ⇒ 𝗏 ⇒ ι ⇒ Φ" ("[_,_]=⇧c⇧k⇧m _") where
  "[w0, v]=⇧c⇧k⇧m i ≡ (λw G. (Vw w0 v) ∧ (R w0 v i) ∧ (cv G w0 v = i))"

abbreviation (input) AtomPhi2 :: "𝗏 ⇒ ι ⇒ Φ" ("[_]=⇧c⇧k⇧m _") where
  "[v]=⇧c⇧k⇧m i ≡ (λw G. (Vw w v) ∧ (R w v i) ∧ (cv G w v = i))"

text ‹The current-world atom X = x is definable as λw G. [w, X] = x.›

definition NegationPhi :: "Φ ⇒ Φ" ("¬⇧c⇧k⇧m _" [52] 53) where
  "¬⇧c⇧k⇧m φ ≡ λw G. ¬ φ w G"

definition ConjunctionPhi :: "Φ ⇒ Φ ⇒ Φ" (infixr "∧⇧c⇧k⇧m" 95) where
  "φ ∧⇧c⇧k⇧m ψ ≡ λw G. φ w G ∧ ψ w G"

definition ImplicationPhi :: "Φ ⇒ Φ ⇒ Φ" (infixr "→⇧c⇧k⇧m" 95) where
  "φ →⇧c⇧k⇧m ψ ≡ λw G. φ w G ⟶ ψ w G"

definition BoxPhi :: "Φ ⇒ Φ" ("□⇧c⇧k⇧m") where
  "□⇧c⇧k⇧m φ ≡ λw G. ∀w'. A w w' ⟶ φ w' G"

definition DiamondPhi :: "Φ ⇒ Φ" ("◇⇧c⇧k⇧m") where
  "◇⇧c⇧k⇧m φ ≡ λw G. ∃w'. A w w' ∧ φ w' G"

text ‹Pointwise well-formedness for a single intervention target/value pair.›
definition wf_intervention :: "𝗐 ⇒ 𝗏 ⇒ ι ⇒ bool" where
  "wf_intervention w v i ≡ Vw w v ∧ R w v i"

lemma wf_intervention_iff [simp]:
  "wf_intervention w v i ⟷ Vw w v ∧ R w v i"
  unfolding wf_intervention_def by simp

text ‹Intervention replaces selected structural equations by constants.›
definition update_F :: "ℱ ⇒ 𝒴 ⇒ (𝗐 ⇒ 𝗏 ⇒ ι) ⇒ ℱ" where
  "update_F G Y b ≡ λw v a. if Y w v ∧ wf_intervention w v (b w v) then b w v else G w v a"

definition Intervention :: "𝒴 ⇒ (𝗐 ⇒ 𝗏 ⇒ ι) ⇒ Φ ⇒ Φ" ("[_←_]_") where
  "[Y ← b] φ ≡ λw G. φ w (update_F G Y b)"

inductive reachable :: "ℱ ⇒ bool" where
  reachable_base [intro]: "reachable F" |
  reachable_step [intro]: "reachable G ⟹ reachable (update_F G Y b)"

lemma directly_depends_const [simp]:
  "¬ directly_depends w v (λ_. (c :: ι)) w1 x"
  by simp

lemma directly_causes_update_subset [simp]:
  assumes "directly_causes (update_F G Y b) w x w1 v"
  shows "directly_causes G w x w1 v" 
  using assms unfolding directly_causes_def update_F_def 
  by metis

definition Truth :: "𝗐 ⇒ ℱ ⇒ Φ ⇒ bool" ("⟨_,_⟩ ⊨⇧c⇧k⇧m _") where
  "⟨w, G⟩ ⊨⇧c⇧k⇧m φ ≡ φ w G"

definition Validity ("⊨⇧c⇧k⇧m _") where
  "⊨⇧c⇧k⇧m φ ≡ ∀w G. W w ⟶ reachable G ⟶ ⟨w, G⟩ ⊨⇧c⇧k⇧m φ"

lemma reachable_update_F [intro]:
  "reachable (update_F F Y b)"
  by (rule reachable_step[OF reachable_base])

lemma reachable_directly_causes_subset_F [simp]:
  assumes rG: "reachable G" and dc: "directly_causes G w x w1 v"
  shows "directly_causes F w x w1 v"
  using assms by (induction) auto

lemma reachable_respects_ranges [simp]:
  assumes "reachable G"
  shows "∀w v t. R w v (G w v t)"
  using assms
  by (induction) (auto simp: equations_respect_ranges update_F_def)

lemma reachable_exo [simp]:
  assumes "reachable G"
  shows "∀w x a. Uw w x ⟶ G w x a = tx w x"
  using assms
  by (induction) (auto simp: exo update_F_def)

lemma reachable_locality [simp]:
  assumes "reachable G"
  shows "∀w1 v a1 a2.
           (∀w x. directly_depends w1 v (G w1 v) w x ⟶ a1 w x = a2 w x) ⟶
           G w1 v a1 = G w1 v a2" 
  using assms 
proof (induction rule: reachable.induct)
  case reachable_base
  then show ?case
    using depends_only_on_direct_causes by blast
next
  case (reachable_step G Y b)
  show ?case 
  proof (intro allI impI) 
    fix w1::𝗐 
    fix v::𝗏
    fix a1 a2::𝗍
    assume H:
      "∀w x. directly_depends w1 v ((update_F G Y b) w1 v) w x ⟶ a1 w x = a2 w x" 
    show "(update_F G Y b) w1 v a1 = (update_F G Y b) w1 v a2" 
    proof (cases "Y w1 v ∧ wf_intervention w1 v (b w1 v)")
      case True
      then show ?thesis
        unfolding update_F_def by simp
    next
      case False
      have H': "∀w x. directly_depends w1 v (G w1 v) w x ⟶ a1 w x = a2 w x"
        using H False unfolding update_F_def apply auto
            apply meson 
            apply blast
            apply meson
            apply meson
            apply meson
            by meson
      have"G w1 v a1 = G w1 v a2"
        using reachable_step.IH H' by blast
      then show ?thesis
        using False unfolding update_F_def by metis
    qed
  qed
qed

lemma reachable_topo_index [simp]:
  assumes rG: "reachable G" and dc: "directly_causes G w x w1 v"
  shows "Uw w x ∨ find_index ord (w, x) < find_index ord (w1, v)"
  by (metis dc rG reachable_directly_causes_subset_F topo_ord)

lemma cv_reachable_endo [simp]:
  assumes rG: "reachable G" and Vwv: "Vw w1 v"
  shows "cv G w1 v = G w1 v (cv G)" 
proof -
  from ord_complete Vwv have vmem: "(w1, v) ∈ set ord"
    by auto
  then obtain prefix suffix where dec: "ord = prefix @ (w1, v) # suffix"
    using split_list 
    by metis
  let ?cpre = "foldl (step_pair G) tx prefix"
  have dist: "distinct (prefix @ (w1, v) # suffix)"
    using ord_distinct dec by simp
  have vnot: "(w1, v) ∉ set suffix"
    using dist by auto
  have cvv: "cv G w1 v = G w1 v ?cpre" 
    by (smt (verit, del_insts) cv_def dec foldl_Cons foldl_append foldl_step_notin fst_conv fun_upd2_same snd_conv step_ctx_def step_pair_def
        vnot)
  have agree: "∀w x. directly_depends w1 v (G w1 v) w x ⟶ ?cpre w x = cv G w x"
  proof (intro allI impI)
    fix w x
    assume dx: "directly_depends w1 v (G w1 v) w x"
    have topo: "Uw w x ∨ find_index ord (w, x) < find_index ord (w1, v)"
      using reachable_topo_index[OF rG] dx unfolding directly_causes_def by blast
    show "?cpre w x = cv G w x" 
    proof (cases "Uw w x")
      case True
      have ord_not: "(w, x) ∉ set ord"
        using True ord_complete by auto
      then have xnotpref: "(w, x) ∉ set prefix"
        using dec 
        by (metis Cons_eq_appendI append_assoc in_set_conv_decomp)
      have cprex: "?cpre w x = tx w x"
        using foldl_step_notin[of "(w, x)" prefix G tx] xnotpref by simp
      have cvx: "cv G w x = tx w x"
        using True by simp
      show ?thesis
        using cprex cvx by simp
    next
      case False
      from dx have Ww: "W w"
        by auto
      have Vx: "Vw w x"
        using False Ww disjoint_variables unfolding Uw_def Vw_def by blast
      have xmem: "(w, x) ∈ set ord"
        using ord_complete Vx by auto
      have idx: "find_index ord (w, x) < find_index ord (w1, v)"
        using topo False by simp
      have idxv: "find_index ord (w1, v) = length prefix"
        unfolding dec by (rule index_at_split[OF dist])
      have idx_lt_pref: "find_index ord (w, x) < length prefix"
        using idx idxv by simp
      have xpref: "(w, x) ∈ set prefix" 
        by (metis dec find_index_nth_if_mem idx_lt_pref nth_append_left nth_mem xmem)
      have xnot: "(w, x) ∉ set ((w1, v) # suffix)"
        using xpref dist by auto
      have cvx: "cv G w x = ?cpre w x" 
      proof -
        have "cv G w x = foldl (step_pair G) (step_pair G ?cpre (w1, v)) suffix w x"
          unfolding cv_def dec by simp
        also have "... = step_pair G ?cpre (w1, v) w x"
          using foldl_step_notin[of "(w, x)" suffix G "step_pair G ?cpre (w1, v)"] xnot by simp
        also have "... = ?cpre w x"
          using xnot unfolding step_pair_def step_ctx_def fun_upd2_def by auto
        finally show ?thesis .
      qed
      then show ?thesis
        by simp
    qed
  qed
  have loc: "G w1 v ?cpre = G w1 v (cv G)"
    using reachable_locality[OF rG] agree by blast
  show ?thesis
    using cvv loc by simp
qed

lemma cv_reachable_fix [simp]:
  assumes rG: "reachable G"
  shows "Fix G (cv G)" 
  using Fix_iff_solution cv_exo cv_outside_model cv_reachable_endo rG by blast

lemma fix_agree_on_ord [simp]:
  assumes rG: "reachable G" and fix1: "Fix G c1" and fix2: "Fix G c2" and pin: "p ∈ set ord"
  shows "c1 (fst p) (snd p) = c2 (fst p) (snd p)"
  using pin 
proof (induction p rule: measure_induct_rule[of "λp. find_index ord p"]) 
  case (less p)
  obtain w v where p_def [simp]: "p = (w, v)"
    by (cases p)
  have pin': "(w, v) ∈ set ord"
    using less.prems by simp
  have Vwv: "Vw w v"
    using ord_complete pin' by auto
  have c1v: "c1 w v = G w v c1"
    using fix1 Vwv unfolding Fix_iff_solution by blast
  have c2v: "c2 w v = G w v c2"
    using fix2 Vwv unfolding Fix_iff_solution by blast
  have agree: "∀w' x. directly_depends w v (G w v) w' x ⟶ c1 w' x = c2 w' x" 
    by (metis (mono_tags, opaque_lifting) Fix_iff_solution case_prod_conv directly_causes_def fix1 fix2 fst_conv less.IH mem_Collect_eq ord_complete
        p_def rG reachable_topo_index snd_conv)
  have "G w v c1 = G w v c2"
    using reachable_locality[OF rG] agree by blast
  with c1v c2v show ?case by simp
qed

lemma fix_agree_endo [simp]:
  assumes rG: "reachable G" and fix1: "Fix G c1" and fix2: "Fix G c2" and Vwv: "Vw w v"
  shows "c1 w v = c2 w v"
  using fix_agree_on_ord[OF rG fix1 fix2] ord_complete Vwv by auto

lemma fix_unique [simp]:
  assumes rG: "reachable G" and fix1: "Fix G c1" and fix2: "Fix G c2"
  shows "c1 = c2" 
  by (metis (no_types, lifting) ext Fix_iff_solution[of G c1] Fix_iff_solution[of G c2] fix1 fix2 fix_agree_endo[of G c1 c2] rG)

lemma reachable_unique_solution [simp]:
  assumes rG: "reachable G"
  shows "∃!ctx. Fix G ctx"
  by (metis cv_reachable_fix fix_unique rG)

lemma cv_eq_if_fix [simp]:
  assumes rG: "reachable G" and fixc: "Fix G c"
  shows "cv G = c"
  using fixc rG by fastforce

lemma cv_intervention_hit [simp]:
  assumes rG: "reachable G" and Ywv: "Y w v" and Vwv: "Vw w v" and Rwv: "R w v (b w v)"
  shows "cv (update_F G Y b) w v = b w v" 
  by (metis (full_types) Rwv Vwv Ywv cv_reachable_endo rG reachable_step update_F_def wf_intervention_iff)

lemma cv_update_range [simp]:
  assumes Vwv: "Vw w v"
  shows "R w v (cv (update_F F Y b) w v)" 
  using assms cv_reachable_endo reachable_respects_ranges reachable_update_F by presburger

lemma fix_strengthen_intervention [simp]:
  assumes base: "Fix (update_F F Y b) c"
      and V1: "Vw w1 v1" and R1: "R w1 v1 i1" and c1: "c w1 v1 = i1"
  shows "Fix (update_F F (fun_upd2 Y w1 v1 True) (fun_upd2 b w1 v1 i1)) c"
  using Fix_iff_solution base c1 update_F_def wf_intervention_def 
  by (smt (verit) fun_upd2_def)

end
