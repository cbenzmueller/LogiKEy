theory IO4CON
  imports IO4 IO_CON
begin

(******************************************************************************)
(* Constrained Input/Output Logic (output 4)                                  *)
(*                                                                            *)
(* Design choices:                                                            *)
(*   1. We keep the unconstrained operators from IO4 intact.                  *)
(*      The constrained layer therefore uses distinct names/slanted aliases:  *)
(*        slantedN  /  ❙◇⇩c                                                   *)
(*        IO4N      /  ❙◇⇧4⇩c                                                 *)
(*   2. Gross output on an input family A is represented directly by          *)
(*        out4 N A ψ  ≡  IO4N N (⋀A) ≤ ψ.                                     *)
(*   3. maxfamily/outfamily follow the usual constrained-I/O presentation.    *)
(******************************************************************************)

definition out4_admissibleN :: "normsys ⇒ (τ ⇒ τ) ⇒ bool"
  where
  "out4_admissibleN N op ≡
      regular_dia op
    ∧ (∀φ. op φ ❙≤ op (φ ❙∧ op φ))
    ∧ (∀φ. op φ ❙≤ slantedN N φ)"

definition largest_out4N :: "normsys ⇒ (τ ⇒ τ) ⇒ bool"
  where
  "largest_out4N N op ≡
      out4_admissibleN N op
    ∧ (∀op1. out4_admissibleN N op1 ⟶ (∀φ. op1 φ ❙≤ op φ))"

consts IO4N :: "normsys ⇒ τ ⇒ τ"

notation IO4N ("❙◇⇧4⇩c")

axiomatization where
  ax_IO4N: "∀N. largest_out4N N (IO4N N)"

lemma IO4N_admissible: "out4_admissibleN N (IO4N N)"
  using ax_IO4N unfolding largest_out4N_def by blast

lemma IO4N_regular: "regular_dia (IO4N N)"
  using IO4N_admissible unfolding out4_admissibleN_def by blast

lemma IO4N_mono: "monotone (IO4N N)"
  using regular_dia_implies_mono IO4N_regular by blast

lemma IO4N_dom: "(IO4N N φ) ❙≤ (slantedN N φ)"
  using IO4N_admissible unfolding out4_admissibleN_def by blast

lemma IO4N_CTineq:
  "(IO4N N φ) ❙≤ (IO4N N (φ ❙∧ IO4N N φ))"
  using IO4N_admissible unfolding out4_admissibleN_def by blast

lemma IO4N_from_norm:
  assumes "N α β"
  shows "(IO4N N α) ❙≤ β"
  using assms IO4N_dom slantedN_from_norm by blast

(* Gross output on a family of factual inputs A. *)
definition out4 :: "normsys ⇒ (τ ⇒ bool) ⇒ τ ⇒ bool"
  where "out4 N A ψ ≡ (IO4N N (❙⋀A)) ❙≤ ψ"

(* Consistency of out4(N,A) with the constraint family C. *)
definition out_consistent :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ bool"
  where "out_consistent N A C ≡ ¬ (((IO4N N (❙⋀A)) ❙∧ (❙⋀C)) = ❙⊥)"

definition maxfamily :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ normsys ⇒ bool"
  where
  "maxfamily N A C N0 ≡
       N0 ❙⊑ N
     ∧ out_consistent N0 A C
     ∧ (∀N1. N0 ❙⊑ N1 ∧ N1 ❙⊑ N ∧ out_consistent N1 A C ⟶ N1 ❙⊑ N0)"

definition outfamily :: "normsys ⇒ (τ ⇒ bool) ⇒ (τ ⇒ bool) ⇒ ((τ ⇒ bool) ⇒ bool)"
  where "outfamily N A C B ≡ ∃N0. maxfamily N A C N0 ∧ B = out4 N0 A"

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
  "outfamily N A C B ⟷ (∃N0. maxfamily N A C N0 ∧ B = out4 N0 A)"
  unfolding outfamily_def by blast

lemma infimum_contains_bottom:
  assumes "S ❙⊥"
  shows "❙⋀S = ❙⊥"
  using assms infimum_member by (auto simp: setfalse_def)

lemma infimum_member_lower:
  assumes "S X"
  shows "❙⋀S ❙≤ X"
  using assms unfolding infimum_def by auto

(* Useful derived rules for the parameterized output-4 operator. *)

lemma IO4N_SI:
  assumes "(IO4N N α) ❙≤ φ"
      and "β ❙≤ α"
  shows "(IO4N N β) ❙≤ φ"
  using IO4N_mono assms unfolding monotone_def by auto

lemma IO4N_WO:
  assumes "(IO4N N α) ❙≤ φ"
      and "φ ❙≤ ψ"
  shows "(IO4N N α) ❙≤ ψ"
  using assms by auto

lemma IO4N_AND:
  assumes "(IO4N N α) ❙≤ φ"
      and "(IO4N N α) ❙≤ ψ"
  shows "(IO4N N α) ❙≤ (φ ❙∧ ψ)"
  using assms by (simp add: setand_def)

lemma IO4N_OR:
  assumes "(IO4N N α) ❙≤ φ"
      and "(IO4N N β) ❙≤ φ"
  shows "(IO4N N (α ❙∨ β)) ❙≤ φ"
proof -
  have reg: "IO4N N (α ❙∨ β) = (IO4N N α ❙∨ IO4N N β)"
    using IO4N_regular unfolding regular_dia_def by blast
  show ?thesis
    using assms reg by (auto simp: setor_def)
qed

lemma IO4N_CT:
  assumes h1: "(IO4N N α) ❙≤ φ"
      and h2: "(IO4N N (α ❙∧ φ)) ❙≤ ψ"
  shows "(IO4N N α) ❙≤ ψ"
proof -
  have fix1: "IO4N N α ❙≤ IO4N N (α ❙∧ IO4N N α)"
    using IO4N_CTineq .
  have le1: "(α ❙∧ IO4N N α) ❙≤ (α ❙∧ φ)"
    using h1 by (simp add: setand_def)
  have mono: "IO4N N (α ❙∧ IO4N N α) ❙≤ IO4N N (α ❙∧ φ)"
    using IO4N_mono le1 unfolding monotone_def by auto
  show ?thesis
    using fix1 mono h2 by auto
qed

lemma IO4N_T:
  assumes h1: "(IO4N N α) ❙≤ φ"
      and h2: "(IO4N N φ) ❙≤ ψ"
  shows "(IO4N N α) ❙≤ ψ" 
proof -
  have le: "(α ❙∧ φ) ❙≤ φ"
    by (simp add: setand_def)
  have m: "IO4N N (α ❙∧ φ) ❙≤ IO4N N φ"
    using IO4N_mono le unfolding monotone_def by auto
  have "IO4N N (α ❙∧ φ) ❙≤ ψ"
    using m h2 by auto
  thus ?thesis
    using IO4N_CT h1 apply auto 
    by blast
qed

(* Gross output as a family of formulas. *)

lemma out4_singletonI:
  assumes "(IO4N N p) ❙≤ ψ"
  shows "out4 N (λx. x = p) ψ"
  by (simp add: assms out4_def)

lemma out4_WO:
  assumes "out4 N A φ"
      and "φ ❙≤ ψ"
  shows "out4 N A ψ"
  using assms unfolding out4_def by blast

lemma out4_bottom_all:
  assumes "out4 N A ❙⊥"
  shows "out4 N A ψ"
  using out4_WO[OF assms] by (simp add: setfalse_def)

lemma not_out_consistent_if_bottom_output:
  assumes "out4 N A ❙⊥"
  shows "¬ out_consistent N A C"
proof -
  have eqbot: "IO4N N (❙⋀A) = ❙⊥"
    using assms unfolding out4_def by (auto simp: setfalse_def)
  show ?thesis
    unfolding out_consistent_def eqbot by (simp add: setand_def setfalse_def)
qed

lemma not_out_consistent_from_output_constraint_conflict:
  assumes outphi: "out4 N A φ"
      and clash: "(φ ❙∧ ❙⋀C) = ❙⊥"
  shows "¬ out_consistent N A C"
proof -
  have outle: "IO4N N (❙⋀A) ❙≤ φ"
    using outphi unfolding out4_def .
  have lebot: "(IO4N N (❙⋀A) ❙∧ ❙⋀C) ❙≤ ❙⊥"
    using outle clash apply (auto simp: setand_def) 
    by metis
  have eqbot: "(IO4N N (❙⋀A) ❙∧ ❙⋀C) = ❙⊥"
    using lebot by (auto simp: setfalse_def)
  show ?thesis
    unfolding out_consistent_def using eqbot by simp
qed

end
