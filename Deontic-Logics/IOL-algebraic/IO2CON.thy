theory IO2CON
  imports IO2 IO_CON
begin

(******************************************************************************)
(* Constrained Input/Output Logic (output 2)                                  *)
(*                                                                            *)
(* Design choices:                                                            *)
(*   1. We keep the unconstrained operators from IO2 intact.                  *)
(*      The constrained layer therefore uses distinct names/slanted aliases:  *)
(*        slantedN  /  ❙◇⇩c                                                   *)
(*        IO2N      /  ❙◇⇧2⇩c                                                 *)
(*   2. Gross output on an input family A is represented directly by          *)
(*        out2 N A ψ  ≡  IO2N N (⋀A) ≤ ψ.                                     *)
(*   3. maxfamily/outfamily follow the usual constrained-I/O presentation.    *)
(******************************************************************************)

definition out2_admissibleN :: "normsys ⇒ (τ ⇒ τ) ⇒ bool"
  where
  "out2_admissibleN N op ≡
      regular_dia op
    ∧ (∀φ. op φ ❙≤ slantedN N φ)"

definition largest_out2N :: "normsys ⇒ (τ ⇒ τ) ⇒ bool"
  where
  "largest_out2N N op ≡
      out2_admissibleN N op
    ∧ (∀op1. out2_admissibleN N op1 ⟶ (∀φ. op1 φ ❙≤ op φ))"

consts IO2N :: "normsys ⇒ τ ⇒ τ" ("❙◇⇧2⇩c")

axiomatization where
  ax_IO2N: "∀N. largest_out2N N (IO2N N)"

lemma IO2N_admissible: "out2_admissibleN N (IO2N N)"
  using ax_IO2N unfolding largest_out2N_def by blast

lemma IO2N_regular: "regular_dia (IO2N N)"
  using IO2N_admissible unfolding out2_admissibleN_def by blast

lemma IO2N_mono: "monotone (IO2N N)"
  using regular_dia_implies_mono IO2N_regular by blast

lemma IO2N_dom: "(IO2N N φ) ❙≤ (slantedN N φ)"
  using IO2N_admissible unfolding out2_admissibleN_def by blast

lemma IO2N_from_norm:
  assumes "N α β"
  shows "(IO2N N α) ❙≤ β"
  using assms IO2N_dom slantedN_from_norm by blast

(* Gross output on a family of factual inputs A. *)
definition out2 :: "normsys ⇒ (τ ⇒ bool) ⇒ τ ⇒ bool"
  where "out2 N A ψ ≡ (IO2N N (❙⋀A)) ❙≤ ψ"

(* Consistency of out2(N,A) with the constraint family C. *)
definition out_consistent :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ bool"
  where "out_consistent N A C ≡ ¬ (((IO2N N (❙⋀A)) ❙∧ (❙⋀C)) = ❙⊥)"

definition maxfamily :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ normsys ⇒ bool"
  where
  "maxfamily N A C N0 ≡
       N0 ❙⊑ N
     ∧ out_consistent N0 A C
     ∧ (∀N1. N0 ❙⊑ N1 ∧ N1 ❙⊑ N ∧ out_consistent N1 A C ⟶ N1 ❙⊑ N0)"

definition outfamily :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ ((τ ⇒ bool) ⇒ bool)"
  where "outfamily N A C B ≡ ∃N0. maxfamily N A C N0 ∧ B = out2 N0 A"

definition skepoutfamily :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ τ ⇒ bool"
  where "skepoutfamily N A C ψ ≡ ∀B. outfamily N A C B ⟶ B ψ"

definition credoutfamily :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ τ ⇒ bool"
  where "credoutfamily N A C ψ ≡ ∃B. outfamily N A C B ∧ B ψ"

abbreviation (input) skep_out_ctd :: "normsys ⇒ (τ ⇒ bool) ⇒ τ ⇒ bool"
  where "skep_out_ctd N A ≡ skepoutfamily N A A"

abbreviation (input) cred_out_ctd :: "normsys ⇒ (τ ⇒ bool) ⇒ τ ⇒ bool"
  where "cred_out_ctd N A ≡ credoutfamily N A A"

lemma maxfamily_subset:
  assumes "maxfamily N A C N0"
  shows "N0 ❙⊑ N"
  using assms unfolding maxfamily_def by blast

lemma maxfamily_consistent:
  assumes "maxfamily N A C N0"
  shows "out_consistent N0 A C"
  using assms unfolding maxfamily_def by blast

lemma outfamily_iff:
  "outfamily N A C B ⟷ (∃N0. maxfamily N A C N0 ∧ B = out2 N0 A)"
  unfolding outfamily_def by blast

lemma infimum_contains_bottom:
  assumes "S ❙⊥"
  shows "❙⋀S = ❙⊥"
  using assms infimum_member by (auto simp: setfalse_def)

lemma infimum_member_lower:
  assumes "S X"
  shows "❙⋀S ❙≤ X"
  using assms unfolding infimum_def by auto

(* Useful derived rules for the parameterized output-2 operator. *)

lemma IO2N_SI:
  assumes "(IO2N N α) ❙≤ φ"
      and "β ❙≤ α"
  shows "(IO2N N β) ❙≤ φ"
  using IO2N_mono assms unfolding monotone_def by auto

lemma IO2N_WO:
  assumes "(IO2N N α) ❙≤ φ"
      and "φ ❙≤ ψ"
  shows "(IO2N N α) ❙≤ ψ"
  using assms by auto

lemma IO2N_AND:
  assumes "(IO2N N α) ❙≤ φ"
      and "(IO2N N α) ❙≤ ψ"
  shows "(IO2N N α) ❙≤ (φ ❙∧ ψ)"
  using assms by (simp add: setand_def)

lemma IO2N_OR:
  assumes "(IO2N N α) ❙≤ φ"
      and "(IO2N N β) ❙≤ φ"
  shows "(IO2N N (α ❙∨ β)) ❙≤ φ"
proof -
  have reg: "IO2N N (α ❙∨ β) = (IO2N N α ❙∨ IO2N N β)"
    using IO2N_regular unfolding regular_dia_def by blast
  show ?thesis
    using assms reg by (auto simp: setor_def)
qed

(* Gross output as a family of formulas. *)

lemma out2_singletonI:
  assumes "(IO2N N p) ❙≤ ψ"
  shows "out2 N (λx. x = p) ψ"
  by (simp add: assms out2_def)

lemma out2_WO:
  assumes "out2 N A φ"
      and "φ ❙≤ ψ"
  shows "out2 N A ψ"
  using assms unfolding out2_def by blast

lemma out2_bottom_all:
  assumes "out2 N A ❙⊥"
  shows "out2 N A ψ"
  using out2_WO[OF assms] by (simp add: setfalse_def)

lemma not_out_consistent_if_bottom_output:
  assumes "out2 N A ❙⊥"
  shows "¬ out_consistent N A C"
proof -
  have eqbot: "IO2N N (❙⋀A) = ❙⊥"
    using assms unfolding out2_def by (auto simp: setfalse_def)
  show ?thesis
    unfolding out_consistent_def eqbot by (simp add: setand_def setfalse_def)
qed

lemma not_out_consistent_from_output_constraint_conflict:
  assumes outphi: "out2 N A φ"
      and clash: "(φ ❙∧ ❙⋀C) = ❙⊥"
  shows "¬ out_consistent N A C"
proof -
  have outle: "IO2N N (❙⋀A) ❙≤ φ"
    using outphi unfolding out2_def .
  have lebot: "(IO2N N (❙⋀A) ❙∧ ❙⋀C) ❙≤ ❙⊥"
    using outle clash by (auto simp: setand_def)
  have eqbot: "(IO2N N (❙⋀A) ❙∧ ❙⋀C) = ❙⊥"
    using lebot by (auto simp: setfalse_def)
  show ?thesis
    unfolding out_consistent_def using eqbot by simp
qed

end
