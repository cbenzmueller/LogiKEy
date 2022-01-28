(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains various meta-theoretical properties of different argumentation semantics. *)
(* Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
 [Dung 1995] Dung, P.M., On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
             logic programming and n-person games, Artificial Intelligence. (1995)
*)
theory "adequacy"
  imports "extensions" "labellings" "Zorn-lemma" "ext-properties" "lab-properties"
begin

(*** Properties as stated in JLC article section 4.2. Lemma numbering as in the article.  ****)
(* -- except for those about correspondences: they are in correspondence.thy
   -- and those about relationships between semantics: they are in ext-relationships.thy and
      lab-relationships.thy. 
*)

(* Lemma 4.3:  no self-attacks in conflict-free extension  [BCG textual on p.8] *)
lemma cf_noselfattacks: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> \<not> (\<exists>\<^sup>\<A> (\<lambda>a. (S a) \<and> (att a a))) \<close> 
  by (simp add: conflictfreeExt_def)

(* Lemma 4.4:  the characteristic function preserves conflict-freeness. *)
lemma cf_preserveChar: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> conflictfreeExt\<^sup>\<A> att (\<F>\<^sup>\<A> att S)\<close>
  by (smt (verit) conflictfreeExt_def defends_rel_def)

(* Lemma 4.5: A conflict-free set S is admissible iff it is a subset of \<F>(S).
   [Dung, Lemma 18] *)
lemma cf_admissibleChar: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> admissibleExt\<^sup>\<A> att S \<longleftrightarrow> S \<subseteq>\<^sup>\<A> \<F>\<^sup>\<A> att S\<close> 
  by (simp add: admissibleExt_def)

(* Lemma 4.6: Admissible sets can be extended with defended arguments (Dung's Fundamental Lemma)
   [Dung, Lemma 10] *)
lemma dung_fundlemma_1: \<open>(admissibleExt\<^sup>\<A> att S) \<and> (defends\<^sup>\<A> att S a) \<Longrightarrow> admissibleExt\<^sup>\<A> att (S \<union> \<lbrace>a\<rbrace>)\<close>
  by (smt (z3) admissibleExt_def conflictfreeExt_def defends_rel_def)

lemma dung_fundlemma_2: \<open>(admissibleExt\<^sup>\<A> att S) \<and> (defends\<^sup>\<A> att S a) \<and> (defends\<^sup>\<A> att S a') \<Longrightarrow> defends\<^sup>\<A> att (S \<union> \<lbrace>a\<rbrace>) a'\<close> 
  by (metis (full_types, lifting) MONO_def \<F>_mono')

(* Lemma 4.7: Admissible sets form a \<omega>-complete CPO wrt. set-inclusion 
   [Dung, Theorem 11, Part (1)] *)
(* We can, in fact, prove a stronger statement: admissible extensions form a dcpo*)
lemma admissibleDirectedComplete: "dcpo\<^sup>\<A> (admissibleExt\<^sup>\<A> AF)" 
  unfolding admissibleExt_def conflictfreeExt_def defends_rel_def directedcomplete_rel_def directed_rel_def
    supremum_def by meson
lemma admissibleOmegaComplete: "\<omega>-cpo\<^sup>\<A> (admissibleExt\<^sup>\<A> AF)" by (simp add: admissibleDirectedComplete dcpo_\<omega>_rel)

(* Lemma 4.8: For each admissible set there exists a preferred extension extending it.
   [Dung, Theorem 11, Part (2)] *)
lemma DungTh11: "admissibleExt\<^sup>\<A> att S \<longrightarrow> (\<exists>E. S \<subseteq>\<^sup>\<A> E \<and> preferredExt\<^sup>\<A> att E)" 
  using ZornLemma2_\<omega>_rel admissibleOmegaComplete  
  by (metis preferredExt2_def preferredExt_defEq)

(* Lemma 4.9: Conflict-free sets are complete iff they are fixed-points of \<F> *)
lemma complete_fix: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> completeExt\<^sup>\<A> att S \<longleftrightarrow> S \<approx>\<^sup>\<A> \<F>\<^sup>\<A> att S\<close> 
  by (metis admissibleExt_def completeExt_def)

(* Lemma 4.10: Complete, preferred and grounded extensions always exist *)
lemma completeExtExists: \<open>\<exists>E. completeExt\<^sup>\<A> att E\<close> 
  by (metis DungTh11 emptyAdmissible maximal_rel_def preferredExt_def)
lemma preferredExtExists: \<open>\<exists>E. preferredExt\<^sup>\<A> att E\<close> 
  by (meson DungTh11 emptyAdmissible maximal_rel_def preferredExt_def)
lemma groundedExtExists: \<open>\<exists>E. groundedExt\<^sup>\<A> att E\<close> 
  by (meson \<F>_leastFP_ex groundedExt3_def groundedExt_defEq1 groundedExt_defEq2 DungTh11 emptyAdmissible minimal_rel_def groundedExt_def)

(* Lemma 4.11: Grounded labellings can equivalently be characterized by minimal in-sets
   and minimal out-sets [BCG11, Prop. 5]*)
lemma complete_sets_mono: \<open>completeLab\<^sup>\<A> att Lab1 \<and> completeLab\<^sup>\<A> att Lab2 \<Longrightarrow> in(Lab1) \<subseteq>\<^sup>\<A> in(Lab2) \<longleftrightarrow> out(Lab1) \<subseteq>\<^sup>\<A> out(Lab2)\<close>
  unfolding completeLab_def inset_def outset_def
  by (smt (z3) Label.exhaust admissibleLab_def inset_def legallyIn_def legallyOut_def legallyUndec_def outset_def undecset_def)

lemma complete_min_inout: \<open>minimal\<^sup>\<A>  (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow> minimal\<^sup>\<A>  (completeLab\<^sup>\<A> att) Lab out \<close>
  by (smt (verit) complete_sets_mono minimal_rel_def)

(* Lemma 4.12: grounded extensions resp. labellings are unique [BCG11, Prop. 4] *)
lemma \<open>groundedExt\<^sup>\<A> att E \<longleftrightarrow> least\<^sup>\<A> (completeExt\<^sup>\<A> att) E id\<close>
  by (simp add: groundedExt2_def groundedExt_defEq1)
lemma \<open>groundedLab\<^sup>\<A> att Lab \<longleftrightarrow> least\<^sup>\<A> (groundedLab\<^sup>\<A> att) Lab in\<close>
  by (metis (full_types) grounded_unique inset_def least_rel_def)

(* Lemma 4.13: Preferred labellings can equivalently be characterized by maximal in-sets
   and maximal out-sets [BCG11, Prop. 8]*)
lemma preferred_max_inout: \<open>maximal\<^sup>\<A>  (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow> maximal\<^sup>\<A>  (completeLab\<^sup>\<A> att) Lab out \<close>
  using prop8 by auto

(* Relationships between different semantics: See ext-relationships.thy and lab-relationships.thy *)
(* Correspondences: See correspondence.thy *)




(* Further properties not mentioned in the article *)
lemma \<open>conflictfreeExt\<^sup>\<A> att S \<and>  minimal\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) S id \<Longrightarrow> lfp\<^sup>\<A> att S  \<close>  
  by (meson \<F>_leastFP_ex lfpR_def minLeastCollapse_rel)

lemma emptyset_is_cf: \<open>conflictfreeExt\<^sup>\<A> att (\<lambda>x. False)\<close> 
  by (simp add: conflictfreeExt_def)

lemma char_is_cf: \<open>conflictfreeExt\<^sup>\<A> att (\<F>\<^sup>\<A> att (\<lambda>x. False))\<close> 
  by (simp add: cf_preserveChar emptyset_is_cf)

lemma \<open> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow>  maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close>
  by (smt (verit) complete_sets_mono maximal_rel_def)

lemma \<open> maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id \<Longrightarrow>  maximal\<^sup>\<A> (completeExt\<^sup>\<A> att) S id\<close>
  unfolding maximal_rel_def completeExt_def admissibleExt_def by (smt (z3) conflictfreeExt_def defends_rel_def id_apply)

end
