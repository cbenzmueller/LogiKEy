theory "ext-simpl-properties"
  imports "extensions-simpl"  "../Zorn-lemma"
begin

(**** Testing definitions for extension-based semantics for argumentation frameworks ***)

section \<open>Admissible and complete extensions - Tests\<close>

(* \<F> is monotone (i.e. order preserving wrt. set inclusion). *)
lemma \<F>_mono: "MONO (\<F> AF)" unfolding MONO_def by (metis defends_def)

(* We can in fact verify that \<F> has both a least and a greatest fixed point. *)
lemma \<F>_leastFP_ex: \<open>\<exists>S. least (fixpoint (\<F> AF)) S id\<close> by (simp add: \<F>_mono wKTl)
lemma \<F>_greatestFP_ex: \<open>\<exists>S. greatest (fixpoint (\<F> AF)) S id\<close> by (simp add: \<F>_mono wKTg)

(* The greatest fixed point is not conflict-free. What about the least? *)
lemma "conflictfreeExt AF (tgfp AF)" (*nitpick*) oops (*countermodel found*)
lemma "conflictfreeExt AF (tlfp AF)" (*nitpick*) oops (*neither proven nor disproven*)

(* Emptyset is admissible*)
lemma emptyAdmissible: \<open>admissibleExt AF \<lbrace>-\<rbrace>\<close> by (simp add: admissibleExt_def conflictfreeExt_def)

(* every complete extension is admissible but not the other way round *)
lemma completeAdmissible: \<open>completeExt AF S \<longrightarrow> admissibleExt AF S\<close> by (simp add: completeExt_def)
lemma \<open>admissibleExt AF S \<Longrightarrow> completeExt AF S\<close> nitpick oops

(* Both definitions for complete extensions coincide *)
lemma completeExt_defEq: "completeExt AF S = completeExt2 AF S" 
  by (metis admissibleExt_def completeExt_def completeExt2_def fixpoint_def)

section \<open>Preferred extensions - Tests\<close>

(* Dung's "Fundamental lemma" ([Dung 1995] Lemma 10) *)
lemma DungFundLemma1: "admissibleExt AF S \<Longrightarrow> \<forall>a. defends AF S a \<longrightarrow> admissibleExt AF  (S \<union> \<lbrace>a\<rbrace>)"
  by (smt (z3) admissibleExt_def conflictfreeExt_def defends_def)
lemma DungFundLemma2: "admissibleExt AF S \<Longrightarrow> \<forall>a b. defends AF S a \<and> defends AF S b \<longrightarrow> defends AF (S \<union> \<lbrace>a\<rbrace>) b"
  by (smt (verit) defends_def)

(* The following lemma is also quite similar in spirit and might be useful to prove subsequent results *)
lemma aux: "admissibleExt AF S \<Longrightarrow> admissibleExt AF  (S \<union> (\<F> AF S))" by (smt (z3) admissibleExt_def conflictfreeExt_def defends_def)

(********* [Dung 1995] Theorem 11: *************)
(*(1) Admissible sets form an \<omega>-complete poset.*)
(* We can, in fact, prove a stronger statement: admissible extensions form a dcpo*)
lemma admissibleDirectedComplete: "dcpo (admissibleExt AF)" 
  unfolding admissibleExt_def conflictfreeExt_def defends_def directedcomplete_def directed_def supremum_def by meson
lemma admissibleOmegaComplete: "\<omega>-cpo (admissibleExt AF)" by (simp add: admissibleDirectedComplete dcpo_\<omega>)

(*(2) For each admissible set S there exists a preferred extension E, such that S \<subseteq> E. *)
lemma DungTh11: "admissibleExt AF S \<longrightarrow> (\<exists>E. S \<subseteq> E \<and> maximal (admissibleExt AF) E id)" 
  by (metis ZornLemma2_\<omega> admissibleOmegaComplete)

(* We can also prove that maximal admissible sets always exist*)
lemma preferredExist: "\<exists>S. maximal (admissibleExt AF) S id" 
  by (simp add: ZornLemma_\<omega> admissibleOmegaComplete)

(* We can verify that maximally admissible extensions are maximally complete extensions; *)
lemma maxAdmissibleComplete: "maximal (admissibleExt AF) S id \<longrightarrow> maximal (completeExt AF) S id"
  unfolding maximal_def completeExt_def admissibleExt_def by (smt (z3) conflictfreeExt_def defends_def id_apply)

(* The converse direction can proven by making use of the previous results*)
lemma maxCompleteAdmissible: "maximal (completeExt AF) S id \<longrightarrow> maximal (admissibleExt AF) S id"
  by (smt (verit) DungTh11 completeAdmissible id_def maxAdmissibleComplete maximal_def)

(* Finally, we can show that both definitions for preferred extensions coincide *)
lemma preferredExt_defEq: "preferredExt AF S \<longleftrightarrow> preferredExt2 AF S"
  unfolding preferredExt2_def preferredExt_def using maxAdmissibleComplete maxCompleteAdmissible by blast

(* Useful lemma: subsets of preferred extensions are conflict-free*)
lemma preferredConflictfree: "A \<subseteq> B \<Longrightarrow> preferredExt AF B \<Longrightarrow> conflictfreeExt AF A"
  by (smt (verit, best) completeExt2_def completeExt_defEq conflictfreeExt_def maximal_def preferredExt_def)


section \<open>Grounded extensions - Tests\<close>

(* The first two definitions of grounded extensions are shown equivalent 
(since \<F> has a least fixed point by the Knaster-Tarski theorem) *)
lemma groundedExt_defEq1: "groundedExt AF S = groundedExt2 AF S" 
  unfolding groundedExt_def groundedExt2_def using \<F>_leastFP_ex by (smt (z3) completeExt2_def completeExt_defEq conflictfreeExt_def id_def least_def minimal_def)

(* A key lemma says that minimal/least fixed points of \<F> are conflict-free. This is not at all trivial! 
 Quite interestingly, SMT solver can prove this by somehow using the existence of preferred extensions.*)
lemma groundedConflictFree: "least (fixpoint (\<F> AF)) S id \<longrightarrow> conflictfreeExt AF S" 
  by (smt (verit, ccfv_threshold) completeExt2_def completeExt_defEq conflictfreeExt_def id_apply least_def maxAdmissibleComplete maximal_def preferredExist)

(* We can show automatically that Dung's definition is equivalent to the other ones*)
lemma groundedExt_defEq2: "groundedExt2 AF S = groundedExt3 AF S"
  by (smt (verit, best) \<F>_mono completeExt2_def completeExt_defEq groundedConflictFree groundedExt2_def groundedExt3_def least_def wKTl')


section \<open>Ideal extensions - Tests\<close>

(* Ideal sets are closed under union *)
lemma idealSetUnion: "idealSet AF A \<Longrightarrow> idealSet AF B \<Longrightarrow> idealSet AF (A\<union>B)" proof -
  assume 1: "idealSet AF A" and 2: "idealSet AF B"
  hence 3: "conflictfreeExt AF (A\<union>B)"
    by (smt (verit) idealSet_def preferredConflictfree preferredExist preferredExt2_def preferredExt_defEq)
  from 1 2 3 show "idealSet AF (A\<union>B)" unfolding idealSet_def preferredExt_def admissibleExt_def by (smt (z3) MONO_def \<F>_mono)
qed

(* both definitions of ideal extensions (i.e. maximal ideal sets) are equivalent *)
lemma idealExt_defEq: "idealExt2 AF S = idealExt AF S" 
  unfolding idealExt_def idealExt2_def maximal_def greatest_def
  using idealSetUnion id_def by (smt (verit, del_insts)) 

section \<open>Stable extensions - Tests\<close>

lemma stableExt_defEq: "stableExt AF S = stableExt2 AF S" 
  by (metis (mono_tags, lifting) range_def conflictfreeExt_def plusset_def stableExt2_def stableExt_def)

section \<open>Semistable extensions - Tests\<close>
(*TODO*)

section \<open>Stage extensions - Tests\<close>
(*TODO*)

end
