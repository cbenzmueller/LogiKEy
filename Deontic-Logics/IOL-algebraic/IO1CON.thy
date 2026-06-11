theory IO1CON
  imports IO1 IO_CON
begin

(******************************************************************************)
(* Constrained Input/Output Logic (output 1)                                  *)
(*                                                                            *)
(* Design choices:                                                            *)
(*   1. We keep the unconstrained operators from IO1 intact.                  *)
(*      The constrained layer therefore uses distinct names/slanted aliases:  *)
(*        slantedN  /  ❙◇⇩c                                                   *)
(*        IO1N      /  ❙◇⇧1⇩c                                                 *)
(*   2. Gross output on an input family A is represented directly by          *)
(*        out1 N A ψ  ≡  IO1N N (⋀A) ≤ ψ.                                     *)
(*   3. maxfamily/outfamily follow the usual constrained-I/O presentation.    *)
(******************************************************************************)

definition out1_admissibleN :: "normsys ⇒ (τ ⇒ τ) ⇒ bool"
  where
  "out1_admissibleN N op ≡
      monotone op
    ∧ (∀φ. op φ ❙≤ slantedN N φ)"

definition largest_out1N :: "normsys ⇒ (τ ⇒ τ) ⇒ bool"
  where
  "largest_out1N N op ≡
      out1_admissibleN N op
    ∧ (∀op1. out1_admissibleN N op1 ⟶ (∀φ. op1 φ ❙≤ op φ))"

consts IO1N :: "normsys ⇒ τ ⇒ τ" ("❙◇⇧1⇩c")

axiomatization where
  ax_IO1N: "∀N. largest_out1N N (IO1N N)"

lemma IO1N_admissible: "out1_admissibleN N (IO1N N)"
  using ax_IO1N unfolding largest_out1N_def by blast

lemma IO1N_mono: "monotone (IO1N N)"
  using IO1N_admissible unfolding out1_admissibleN_def by blast

lemma IO1N_dom: "(IO1N N φ) ❙≤ (slantedN N φ)"
  using IO1N_admissible unfolding out1_admissibleN_def by blast

lemma IO1N_from_norm:
  assumes "N α β"
  shows "(IO1N N α) ❙≤ β"
  using assms IO1N_dom slantedN_from_norm by blast

(* Gross output on a family of factual inputs A. *)
definition out1 :: "normsys ⇒ (τ ⇒ bool) ⇒ τ ⇒ bool"
  where "out1 N A ψ ≡ (IO1N N (❙⋀A)) ❙≤ ψ"

(* Consistency of out1(N,A) with the constraint family C. *)
definition out_consistent :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ bool"
  where "out_consistent N A C ≡ ¬ (((IO1N N (❙⋀A)) ❙∧ (❙⋀C)) = ❙⊥)"

definition maxfamily :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ normsys ⇒ bool"
  where
  "maxfamily N A C N0 ≡
       N0 ❙⊑ N
     ∧ out_consistent N0 A C
     ∧ (∀N1. N0 ❙⊑ N1 ∧ N1 ❙⊑ N ∧ out_consistent N1 A C ⟶ N1 ❙⊑ N0)"

definition outfamily :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ ((τ ⇒ bool) ⇒ bool)"
  where "outfamily N A C B ≡ ∃N0. maxfamily N A C N0 ∧ B = out1 N0 A"

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
  "outfamily N A C B ⟷ (∃N0. maxfamily N A C N0 ∧ B = out1 N0 A)"
  unfolding outfamily_def by blast

lemma infimum_contains_bottom:
  assumes "S ❙⊥"
  shows "❙⋀S = ❙⊥"
  using assms infimum_member by (auto simp: setfalse_def)

lemma infimum_member_lower:
  assumes "S X"
  shows "❙⋀S ❙≤ X"
  using assms unfolding infimum_def by auto

(* Useful derived rules for the parameterized output-1 operator. *)

lemma IO1N_SI:
  assumes "(IO1N N α) ❙≤ φ"
      and "β ❙≤ α"
  shows "(IO1N N β) ❙≤ φ"
  using IO1N_mono assms unfolding monotone_def by auto

lemma IO1N_WO:
  assumes "(IO1N N α) ❙≤ φ"
      and "φ ❙≤ ψ"
  shows "(IO1N N α) ❙≤ ψ"
  using assms by auto

lemma IO1N_AND:
  assumes "(IO1N N α) ❙≤ φ"
      and "(IO1N N α) ❙≤ ψ"
  shows "(IO1N N α) ❙≤ (φ ❙∧ ψ)"
  using assms by (simp add: setand_def)

(* Gross output as a family of formulas. *)

lemma out1_singletonI:
  assumes "(IO1N N p) ❙≤ ψ"
  shows "out1 N (λx. x = p) ψ"
  by (simp add: assms out1_def)

lemma out1_WO:
  assumes "out1 N A φ"
      and "φ ❙≤ ψ"
  shows "out1 N A ψ"
  using assms unfolding out1_def by blast

lemma out1_bottom_all:
  assumes "out1 N A ❙⊥"
  shows "out1 N A ψ"
  using out1_WO[OF assms] by (simp add: setfalse_def)

lemma not_out_consistent_if_bottom_output:
  assumes "out1 N A ❙⊥"
  shows "¬ out_consistent N A C"
proof -
  have eqbot: "IO1N N (❙⋀A) = ❙⊥"
    using assms unfolding out1_def by (auto simp: setfalse_def)
  show ?thesis
    unfolding out_consistent_def eqbot by (simp add: setand_def setfalse_def)
qed

lemma not_out_consistent_from_output_constraint_conflict:
  assumes outphi: "out1 N A φ"
      and clash: "(φ ❙∧ ❙⋀C) = ❙⊥"
  shows "¬ out_consistent N A C" 
proof -
  have outle: "IO1N N (❙⋀A) ❙≤ φ"
    using outphi unfolding out1_def .
  have lebot: "(IO1N N (❙⋀A) ❙∧ ❙⋀C) ❙≤ ❙⊥"
    using outle clash apply (auto simp: setand_def) 
    by metis
  have eqbot: "(IO1N N (❙⋀A) ❙∧ ❙⋀C) = ❙⊥"
    using lebot by (auto simp: setfalse_def)
  show ?thesis
    unfolding out_consistent_def using eqbot by simp
qed

end
