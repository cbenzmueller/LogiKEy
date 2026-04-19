(* Luca Pasetto, Roberts Tarvids, Apostolos Tzimoulis and Christoph Benzmüller, 2026 *)
theory CKM_axioms_test
  imports CKM
begin

lemma True
  nitpick[satisfy]
  oops

text ‹
  Axiom checks for the causal-Kripke embedding.

  Since the current-world atom X = x is definable as λw G. [w, X] = x, we test the
  world-indexed fragment directly. This is the part that is essential for interventions,
  the modal axioms, and the C5-style recursiveness principle.
›

lemma equality [simp]:
  "∀w w0 v x x' Y b.
      x ≠ x' ⟶
      ⟨w, F⟩ ⊨⇧c⇧k⇧m 
           (ImplicationPhi
           (Intervention Y b ([w0, v]=⇧c⇧k⇧m x))
           (NegationPhi (Intervention Y b ([w0, v]=⇧c⇧k⇧m x'))))"
  by (simp add: AtomPhi_def ImplicationPhi_def Intervention_def NegationPhi_def Truth_def)

lemma definiteness [simp]:
  "∀w w0 v Y b. Vw w0 v ⟶ (∃i. R w0 v i ∧ ⟨w, F⟩ ⊨⇧c⇧k⇧m (Intervention Y b ([w0, v]=⇧c⇧k⇧m i)))"
  unfolding Truth_def AtomPhi_def Intervention_def
  using cv_update_range by blast

lemma composition [simp]:
  "∀w w1 v1 w2 v2 i1 i2 Y b.
      ((Vw w1 v1 ∧ Vw w2 v2) ∧
       ⟨w, F⟩ ⊨⇧c⇧k⇧m (Intervention Y b ([w1, v1]=⇧c⇧k⇧m i1)) ∧
       ⟨w, F⟩ ⊨⇧c⇧k⇧m (Intervention Y b ([w2, v2]=⇧c⇧k⇧m i2)))
      ⟶
       ⟨w, F⟩ ⊨⇧c⇧k⇧m
         (Intervention (fun_upd2 Y w1 v1 True) (fun_upd2 b w1 v1 i1) ([w2, v2]=⇧c⇧k⇧m i2))" 
  by (smt (z3) AtomPhi_def Intervention_def Truth_def cv_reachable_fix fix_agree_endo
      fix_strengthen_intervention reachable_update_F)

lemma effectiveness [simp]:
  "∀w w0 v i Y b. (Vw w0 v ∧ R w0 v i) ⟶
      ⟨w, F⟩ ⊨⇧c⇧k⇧m
        (Intervention (fun_upd2 Y w0 v True) (fun_upd2 b w0 v i) ([w0, v]=⇧c⇧k⇧m i))"
  by (simp add: AtomPhi_def Intervention_def Truth_def reachable_base)

lemma effectiveness_single [simp]:
  "∀w w0 v i. (Vw w0 v ∧ R w0 v i) ⟶
      ⟨w, F⟩ ⊨⇧c⇧k⇧m
        (Intervention (fun_upd2 (λ_ _. False) w0 v True) (fun_upd2 tx w0 v i) ([w0, v]=⇧c⇧k⇧m i))"
  using effectiveness by blast

lemma C5_recursiveness:
  "∀w x w1 v. (w, x) ≠ (w1, v) ⟶
      ((Uw w x ∧ Vw w1 v) ∨ (Vw w x ∧ Vw w1 v ∧ find_index ord (w, x) < find_index ord (w1, v))) ⟶
      ¬ ((Uw w1 v ∧ Vw w x) ∨ (Vw w1 v ∧ Vw w x ∧ find_index ord (w1, v) < find_index ord (w, x)))"
  using recur_ord by blast

lemma recursiveness_direct:
  "∀w x w1 v.
      directly_causes F w x w1 v ⟶ ¬ directly_causes F w1 v w x" 
  by (metis directly_causes_def exo order_less_imp_not_less topo_ord)

lemma determinism_neg_lit [simp]:
  "∀w w0 v i Y b.
      (⟨w, F⟩ ⊨⇧c⇧k⇧m (Intervention Y b (NegationPhi ([w0, v]=⇧c⇧k⇧m i)))) ⟷
      (⟨w, F⟩ ⊨⇧c⇧k⇧m (NegationPhi (Intervention Y b ([w0, v]=⇧c⇧k⇧m i))))"
  by (simp add: Intervention_def NegationPhi_def Truth_def)

lemma determinism_neg [simp]:
  "∀w Y b φ.
      (⟨w, F⟩ ⊨⇧c⇧k⇧m (Intervention Y b (NegationPhi φ))) ⟷
      (⟨w, F⟩ ⊨⇧c⇧k⇧m (NegationPhi (Intervention Y b φ)))"
  by (simp add: Intervention_def NegationPhi_def Truth_def)

lemma determinism_conj_lit [simp]:
  "∀w w1 v1 i1 w2 v2 i2 Y b.
      (⟨w, F⟩ ⊨⇧c⇧k⇧m
         (Intervention Y b (ConjunctionPhi ([w1, v1]=⇧c⇧k⇧m i1) ([w2, v2]=⇧c⇧k⇧m i2)))) ⟷
      (⟨w, F⟩ ⊨⇧c⇧k⇧m
         (ConjunctionPhi (Intervention Y b ([w1, v1]=⇧c⇧k⇧m i1)) (Intervention Y b ([w2, v2]=⇧c⇧k⇧m i2))))"
  by (simp add: ConjunctionPhi_def Intervention_def Truth_def)

lemma determinism_conj [simp]:
  "∀w Y b φ ψ.
      (⟨w, F⟩ ⊨⇧c⇧k⇧m (Intervention Y b (ConjunctionPhi φ ψ))) ⟷
      (⟨w, F⟩ ⊨⇧c⇧k⇧m (ConjunctionPhi (Intervention Y b φ) (Intervention Y b ψ)))"
  by (simp add: ConjunctionPhi_def Intervention_def Truth_def)

lemma MP [simp]:
  "∀w φ ψ. (⟨w, F⟩ ⊨⇧c⇧k⇧m φ ∧ ⟨w, F⟩ ⊨⇧c⇧k⇧m (ImplicationPhi φ ψ)) ⟶ ⟨w, F⟩ ⊨⇧c⇧k⇧m ψ"
  by (simp add: ImplicationPhi_def Truth_def)

text ‹Modal axioms from the causal-Kripke paper.›

lemma K_axiom [simp]:
  "⊨⇧c⇧k⇧m (ImplicationPhi (BoxPhi (ImplicationPhi φ ψ)) (ImplicationPhi (BoxPhi φ) (BoxPhi ψ)))"
  by (simp add: BoxPhi_def ImplicationPhi_def Truth_def Validity_def)

lemma box_axiom [simp]:
  "∀w G Y b φ. W w ⟶ reachable G ⟶
      (⟨w, G⟩ ⊨⇧c⇧k⇧m (Intervention Y b (BoxPhi φ))) ⟷
      (⟨w, G⟩ ⊨⇧c⇧k⇧m (BoxPhi (Intervention Y b φ)))"
  by (simp add: BoxPhi_def Intervention_def Truth_def)

lemma diamond_axiom [simp]:
  "∀w G Y b φ. W w ⟶ reachable G ⟶
      (⟨w, G⟩ ⊨⇧c⇧k⇧m (Intervention Y b (DiamondPhi φ))) ⟷
      (⟨w, G⟩ ⊨⇧c⇧k⇧m (DiamondPhi (Intervention Y b φ)))"
  by (simp add: DiamondPhi_def Intervention_def Truth_def)

lemma G_axiom [simp]:
  "∀w0 v i Y b.
      ⊨⇧c⇧k⇧m (ImplicationPhi (Intervention Y b ([w0, v]=⇧c⇧k⇧m i)) (BoxPhi (Intervention Y b ([w0, v]=⇧c⇧k⇧m i))))"
  unfolding Validity_def Truth_def ImplicationPhi_def BoxPhi_def Intervention_def AtomPhi_def
  by blast

end
