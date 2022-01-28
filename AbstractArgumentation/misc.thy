(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains miscellaneous basic definition used throughout the work. *)
theory misc
  imports Main 
begin

(* Technical detail: default settings to use for model finder Nitpick (inherited by all downstream theories) *)
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2, atoms= a b c d]

declare [[syntax_ambiguity_warning = false]] 

(************** Basic set- and order-theoretical notions ******************)

(* hide set notation for Isabelle's built-in sets: The aim is to provide an 
   embedding that is as shallow as possible (i.e., it uses no representation
   techniques that are specific to Isabelle/HOL. Still, we want to 
   use nice notation; this is why Isabelle/HOL predefined interpretations for 
   subset, union, etc. symbols are hidden. *)
no_notation
  subset  ("'(\<subset>')") and
  subset  ("(_/ \<subset> _)" [51, 51] 50) and
  subset_eq  ("'(\<subseteq>')") and
  subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) and
  union (infixl "\<union>" 65) and
  inter (infixl "\<inter>" 70)

(* Sets and relations are vanilla type-polymorphic predicates.
   'a is a type variable representing an arbitrary type.
   Both notions are repreesnted by their respective characteristic
   functions. *)
(*sets as functions into a 2-element codomain *)
type_synonym 'a Set = \<open>'a \<Rightarrow> bool\<close> 
(*relations as curried 2-ary functions into a 2-element codomain *)
type_synonym 'a Rel = \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>

(* Introduce useful set operations and shorthand.
   They only make use of plain higher-order terms.
   Some of the symbols are, for presentation purposes, defined
   as infix symbols (using Isabelle/HOLs representation syntax);
   this is just syntactical sugar. *)
abbreviation union::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> (infixl "\<union>" 53) where \<open>A \<union> B \<equiv> \<lambda>x. (A x \<or> B x)\<close>
abbreviation inter::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> (infixl "\<inter>" 54) where \<open>A \<inter> B \<equiv> \<lambda>x. (A x \<and> B x)\<close>
abbreviation compl::\<open>'a Set \<Rightarrow> 'a Set\<close> ("\<midarrow>_") where \<open>\<midarrow>A \<equiv> \<lambda>x. \<not>A x\<close>
abbreviation inclusion::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> bool\<close> (infix "\<subseteq>" 52) where \<open>A \<subseteq> B \<equiv> \<forall>x. (A x \<longrightarrow> B x)\<close>
abbreviation inclusion_rel::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("_\<subseteq>\<^sup>__") where \<open>A \<subseteq>\<^sup>U B \<equiv> \<forall>x. U x \<longrightarrow> (A x \<longrightarrow> B x)\<close>
abbreviation equ::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> bool\<close> (infix "\<approx>" 55) where \<open>A \<approx> B \<equiv> \<forall>x. (A x \<longleftrightarrow> B x)\<close>
abbreviation equ_rel::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("_\<approx>\<^sup>__") where \<open>A \<approx>\<^sup>U B \<equiv> \<forall>x. U x \<longrightarrow> (A x \<longleftrightarrow> B x)\<close>
abbreviation proper_inclusion::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow>bool\<close> (infix "\<subset>" 52) where \<open>A \<subset> B \<equiv> (A \<subseteq> B) \<and> \<not>(A\<approx>B)\<close>
abbreviation proper_inclusion_rel::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set \<Rightarrow>bool\<close> ("_\<subset>\<^sup>__") where \<open>A \<subset>\<^sup>U B \<equiv> (A \<subseteq>\<^sup>U B) \<and> \<not>(A \<approx>\<^sup>U B)\<close>
abbreviation set_cnstr0::\<open>'a Set\<close> ("\<lbrace>-\<rbrace>") where \<open>\<lbrace>-\<rbrace> \<equiv> \<lambda>x. False\<close>
abbreviation set_cnstr1::\<open>'a\<Rightarrow>'a Set\<close> ("\<lbrace>_\<rbrace>") where \<open>\<lbrace>a\<rbrace> \<equiv> \<lambda>x. x = a\<close>
abbreviation set_cnstr2::\<open>'a\<Rightarrow>'a\<Rightarrow>'a Set\<close> ("\<lbrace>_,_\<rbrace>") where \<open>\<lbrace>a,b\<rbrace> \<equiv> \<lambda>x. x = a \<or> x = b\<close>
abbreviation set_cnstr3::\<open>'a\<Rightarrow>'a\<Rightarrow>'a\<Rightarrow>'a Set\<close> ("\<lbrace>_,_,_\<rbrace>") where \<open>\<lbrace>a,b,c\<rbrace> \<equiv> \<lambda>x. x = a \<or> x = b \<or> x = c\<close>

(*TODO: is it possible to also add binder notation to the ones below?*)
(*Restricted quantifiers that take a 'domain' as additional parameter (interpreted as the predicate 'exists')*)
abbreviation mforall_rel::"('a\<Rightarrow>bool)\<Rightarrow>('a\<Rightarrow>bool)\<Rightarrow>bool" ("\<forall>\<^sup>_ _") where \<open>\<forall>\<^sup>U P \<equiv> \<forall>x. U x \<longrightarrow> (P x)\<close> 
abbreviation mexists_rel::"('a\<Rightarrow>bool)\<Rightarrow>('a\<Rightarrow>bool)\<Rightarrow>bool" ("\<exists>\<^sup>_ _") where \<open>\<exists>\<^sup>U P \<equiv> \<exists>x. U x  \<and>  (P x)\<close>
lemma relQuantifierDual: \<open>\<forall>\<^sup>A P \<longleftrightarrow> \<not>(\<exists>\<^sup>A (\<lambda>x. \<not>(P x)))\<close> by simp

(* abbreviation mforall_relB (binder "\<forall>\<^sup>_" [55]56) where "\<forall>\<^sup>U x. P x \<equiv> \<forall>\<^sup>U P" *)
(* abbreviation mexists_relB (binder "\<exists>\<^sup>_" [55]56) where "\<exists>\<^sup>U x. P x \<equiv> \<exists>\<^sup>U P" *)

lemma \<open>A \<subset>\<^sup>U B \<longrightarrow> A \<subset> B\<close> nitpick oops
lemma \<open>A \<subset> B \<longrightarrow> A \<subset>\<^sup>U B\<close> nitpick oops
lemma \<open>A \<subseteq>\<^sup>U B \<longrightarrow> A \<subseteq> B\<close> nitpick oops
lemma subs_rel: \<open>A \<subseteq> B \<Longrightarrow> A \<subseteq>\<^sup>U B\<close> by simp

(* and some generic notions for representing minimal and maximal (resp.least and greatest) sets wrt. set inclusion: *)
definition  \<open>minimal Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<and>  E(X)  \<subseteq> E(Obj) \<longrightarrow> E(X) \<approx> E(Obj))\<close>
definition  \<open>maximal Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<and> E(Obj) \<subseteq>  E(X)  \<longrightarrow> E(X) \<approx> E(Obj))\<close>
definition    \<open>least Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<longrightarrow> E(Obj) \<subseteq> E(X))\<close>
definition \<open>greatest Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<longrightarrow>  E(X)  \<subseteq> E(Obj))\<close>

definition minimal_rel ("minimal\<^sup>_ _ _ _") 
  where \<open>minimal\<^sup>U Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<and> (E X) \<subseteq>\<^sup>U (E Obj) \<longrightarrow> (E X) \<approx>\<^sup>U (E Obj))\<close>
definition maximal_rel ("maximal\<^sup>_ _ _ _") 
  where \<open>maximal\<^sup>U Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<and> (E Obj) \<subseteq>\<^sup>U (E X) \<longrightarrow> (E X) \<approx>\<^sup>U (E Obj))\<close>
definition least_rel ("least\<^sup>_ _ _ _") 
  where \<open>least\<^sup>U Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<longrightarrow> (E Obj) \<subseteq>\<^sup>U (E X))\<close>
definition greatest_rel ("greatest\<^sup>_ _ _ _")
  where \<open>greatest\<^sup>U Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<longrightarrow> (E X) \<subseteq>\<^sup>U (E Obj))\<close>

(* Verified: Least (resp. greatest) sets are minimal (resp. maximal) but not the other way round. *)
lemma leastMin: \<open>least Prop Obj E \<longrightarrow>  minimal Prop Obj E\<close> unfolding least_def minimal_def by blast
lemma leastMin_rel: \<open>least\<^sup>U Prop Obj E \<longrightarrow>  minimal\<^sup>U Prop Obj E\<close> unfolding least_rel_def minimal_rel_def by blast
lemma greatestMax: \<open>greatest Prop Obj E \<longrightarrow>  maximal Prop Obj E\<close> unfolding greatest_def maximal_def by blast
lemma greatestMax_rel: \<open>greatest\<^sup>U Prop Obj E \<longrightarrow>  maximal\<^sup>U Prop Obj E\<close> unfolding greatest_rel_def maximal_rel_def by blast
lemma  \<open>minimal Prop Obj E \<longrightarrow>  least Prop Obj E\<close> nitpick oops (* countermodel found *)
lemma  \<open>minimal\<^sup>U Prop Obj E \<longrightarrow> least\<^sup>U Prop Obj E\<close> nitpick oops (* countermodel found *)
lemma  \<open>maximal Prop Obj E \<longrightarrow> greatest Prop Obj E\<close> nitpick oops (* countermodel found *)
lemma  \<open>maximal\<^sup>U Prop Obj E \<longrightarrow> greatest\<^sup>U Prop Obj E\<close> nitpick oops (* countermodel found *)

lemma \<open>minimal Prop Obj E \<longrightarrow> minimal\<^sup>U Prop Obj E\<close> nitpick oops
lemma \<open>minimal\<^sup>U Prop Obj E \<longrightarrow> minimal Prop Obj E\<close> nitpick oops
lemma \<open>maximal Prop Obj E \<longrightarrow> maximal\<^sup>U Prop Obj E\<close> nitpick oops
lemma \<open>maximal\<^sup>U Prop Obj E \<longrightarrow> maximal Prop Obj E\<close> nitpick oops
lemma least_rel_impl:    \<open>least Prop Obj E \<longrightarrow> least\<^sup>U Prop Obj E\<close> by (simp add: least_def least_rel_def)
lemma greatest_rel_impl: \<open>greatest Prop Obj E \<longrightarrow> greatest\<^sup>U Prop Obj E\<close> by (simp add: greatest_def greatest_rel_def)

(* Verified: Least and greatest elements are unique (wrt. their extensions by E). *)
lemma leastUnique:      \<open>least Prop A E \<and> least Prop B E \<longrightarrow> E(A) \<approx> E(B)\<close> by (metis least_def)
lemma leastUnique_rel: \<open>least\<^sup>U Prop A E \<and> least\<^sup>U Prop B E \<longrightarrow> E(A) \<approx>\<^sup>U E(B)\<close> by (metis least_rel_def)
lemma greatestUnique:      \<open>greatest Prop A E \<and> greatest Prop B E \<longrightarrow> E(A) \<approx> E(B)\<close> by (metis greatest_def)
lemma greatestUnique_rel: \<open>greatest\<^sup>U Prop A E \<and> greatest\<^sup>U Prop B E \<longrightarrow> E(A) \<approx>\<^sup>U E(B)\<close> by (metis greatest_rel_def)

(* Verified: If there exists a least/greatest element then minimal/maximal collapse to least/greatest. *)
lemma minLeastCollapse:      \<open>\<exists>A. least Prop A E \<Longrightarrow> \<forall>B. minimal Prop B E \<longrightarrow>  least Prop B E\<close> 
  by (smt (verit, best) least_def minimal_def)
lemma minLeastCollapse_rel: \<open>\<exists>A. least\<^sup>U Prop A E \<Longrightarrow> \<forall>B. minimal\<^sup>U Prop B E \<longrightarrow>  least\<^sup>U Prop B E\<close> 
  by (smt (verit, best) least_rel_def minimal_rel_def)
lemma maxGreatestCollapse:      \<open>\<exists>A. greatest Prop A E \<Longrightarrow> \<forall>B. maximal Prop B E \<longrightarrow>  greatest Prop B E\<close> 
  by (smt (verit, best) greatest_def maximal_def)
lemma maxGreatestCollapse_rel: \<open>\<exists>A. greatest\<^sup>U Prop A E \<Longrightarrow> \<forall>B. maximal\<^sup>U Prop B E \<longrightarrow>  greatest\<^sup>U Prop B E\<close> 
  by (smt (verit, best) greatest_rel_def maximal_rel_def)


(* In what follows we verify some useful results concerning the existence of least/greatest fixed points of monotone functions. *)
(* We start by defining infinite meet (infimum) and infinite join (supremum) operations,*)
definition infimum::  \<open>'a Set Set \<Rightarrow> 'a Set\<close> ("\<^bold>\<And>_") where \<open>\<^bold>\<And>S \<equiv> \<lambda>w. \<forall>X. S X \<longrightarrow> X w\<close>
definition supremum:: \<open>'a Set Set \<Rightarrow> 'a Set\<close> ("\<^bold>\<Or>_") where \<open>\<^bold>\<Or>S \<equiv> \<lambda>w. \<exists>X. S X  \<and>  X w\<close>

definition upper_bound ("UB") where \<open>UB S \<equiv> \<lambda>A. \<forall>X. S X \<longrightarrow> X \<subseteq> A\<close>
definition upper_bound_rel ("UB\<^sup>_") where \<open>UB\<^sup>U S \<equiv> \<lambda>A. \<forall>X. S X \<longrightarrow> (X \<subseteq>\<^sup>U A)\<close>
lemma ub_rel_impl: \<open>UB S x \<Longrightarrow> UB\<^sup>U S x\<close> by (simp add: upper_bound_def upper_bound_rel_def)

definition lower_bound ("LB") where \<open>LB S \<equiv> \<lambda>A. \<forall>X. S X \<longrightarrow> A \<subseteq> X\<close>
definition lower_bound_rel ("LB\<^sup>_") where \<open>LB\<^sup>U S \<equiv> \<lambda>A. \<forall>X. S X \<longrightarrow> (A \<subseteq>\<^sup>U X)\<close>
abbreviation \<open>is_supremum S U \<equiv> least (UB S) U id\<close>
abbreviation \<open>is_infimum  S L \<equiv> greatest (LB S) L id\<close>

(* ... and show that the corresponding lattice is complete: *)
lemma sup_char: \<open>is_supremum S \<^bold>\<Or>S\<close> unfolding supremum_def least_def upper_bound_def by auto
lemma inf_char: \<open>is_infimum S \<^bold>\<And>S\<close> unfolding infimum_def greatest_def lower_bound_def by auto

lemma sup_char_rel: \<open>is_supremum (S \<inter> U) (\<^bold>\<Or>S \<inter> U) \<close> by (simp add: sup_char)
lemma inf_char_rel: \<open>is_infimum (S \<inter> U) (\<^bold>\<And>S \<inter> U) \<close> by (simp add: inf_char)

(* Definition of a monotone function.*)
definition \<open>MONO F \<equiv> \<forall>A B. A \<subseteq> B \<longrightarrow> F A \<subseteq> F B\<close>
definition MONO_rel ("MONO\<^sup>_") where \<open>MONO\<^sup>U F \<equiv> \<forall>A B. (A \<subseteq>\<^sup>U B \<longrightarrow> F A \<subseteq>\<^sup>U F B)\<close>

(* We speak of argument-sets being fixed points of functions (mapping argument-sets to argument-sets).
For a given function we define in the usual way a fixed-point predicate for argument-sets.*)
definition fixpoint :: \<open>('a Set \<Rightarrow> 'a Set) \<Rightarrow> 'a Set \<Rightarrow> bool\<close> 
  where \<open>fixpoint \<phi> \<equiv> \<lambda>S. \<phi>(S) \<approx>  S\<close>
definition fixpoint_rel:: \<open>'a Set \<Rightarrow> ('a Set \<Rightarrow> 'a Set) \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("fixpoint\<^sup>_")
  where \<open>fixpoint\<^sup>U \<phi> \<equiv> \<lambda>S. \<phi>(S) \<approx>\<^sup>U S\<close>

lemma fp_prop1: \<open>fixpoint \<phi> S \<Longrightarrow> fixpoint\<^sup>U \<phi> S\<close> by (simp add: fixpoint_rel_def fixpoint_def)
lemma fp_prop2: \<open>\<forall>U. least\<^sup>U (\<lambda>S. fixpoint\<^sup>U F S) S id \<Longrightarrow> least (fixpoint F) S id\<close> unfolding fixpoint_rel_def fixpoint_def least_def least_rel_def by metis

(* Verified: Least/Greatest fixedpoint is indeed a fixedpoint and is least/greatest. *)
lemma    \<open>(least (fixpoint F) S id) = (fixpoint F S \<and> (\<forall>X. fixpoint F X \<longrightarrow> S \<subseteq> X))\<close> by (simp add: least_def)
lemma \<open>(greatest (fixpoint F) S id) = (fixpoint F S \<and> (\<forall>X. fixpoint F X \<longrightarrow> X \<subseteq> S))\<close> by (simp add: greatest_def)

(* A weak formulation of the Knaster-Tarski Theorem:
 Any monotone function on a powerset lattice has a least/greatest fixed-point.*)
lemma wKTl': \<open>MONO F \<Longrightarrow> let S = \<^bold>\<And>(\<lambda>X. F X \<subseteq> X) in (least (fixpoint F) S id)\<close>
  unfolding least_def fixpoint_def MONO_def by (smt (z3) eq_id_iff infimum_def)
lemma wKTg': \<open>MONO F \<Longrightarrow> let S = \<^bold>\<Or>(\<lambda>X. X \<subseteq> F X) in (greatest (fixpoint F) S id)\<close>
  unfolding greatest_def fixpoint_def MONO_def by (smt (z3) eq_id_iff supremum_def)
lemma wKTl:  \<open>MONO F \<Longrightarrow> \<exists>S. least (fixpoint F) S id\<close> using wKTl' by auto
lemma wKTg:  \<open>MONO F \<Longrightarrow> \<exists>S. greatest (fixpoint F) S id\<close> using wKTg' by auto

lemma wKTl_rel': \<open>MONO\<^sup>U F \<Longrightarrow> let S = \<^bold>\<And>(\<lambda>X. F X \<subseteq>\<^sup>U X) in (least (fixpoint\<^sup>U F) S id)\<close> 
  unfolding MONO_rel_def fixpoint_rel_def least_def by (smt (z3) eq_id_iff infimum_def)
lemma wKTg_rel': \<open>MONO\<^sup>U F \<Longrightarrow> let S = \<^bold>\<Or>(\<lambda>X. X \<subseteq>\<^sup>U F X) in (greatest (fixpoint\<^sup>U F) S id)\<close>
  unfolding MONO_rel_def fixpoint_rel_def greatest_def by (smt (z3) eq_id_iff supremum_def)

lemma wKTl_rel: \<open>MONO\<^sup>U F \<Longrightarrow> \<exists>S. least (fixpoint\<^sup>U F) S id\<close> using wKTl_rel' by auto
lemma wKTl_relw: \<open>MONO\<^sup>U F \<Longrightarrow> \<exists>S. least\<^sup>U (fixpoint\<^sup>U F) S id\<close> using wKTl_rel by (metis least_rel_impl)
lemma wKTg_rel: \<open>MONO\<^sup>U F \<Longrightarrow> \<exists>S. greatest (fixpoint\<^sup>U F) S id\<close> using wKTg_rel' by auto
lemma wKTg_relw: \<open>MONO\<^sup>U F \<Longrightarrow> \<exists>S. greatest\<^sup>U (fixpoint\<^sup>U F) S id\<close> using wKTg_rel by (metis greatest_rel_impl)


(* Directed sets are sets for which each pair of elements have an upper bound in the set*)
definition directed :: "'a Set Set \<Rightarrow> bool" 
  where "directed S \<equiv> \<forall>A B. S A \<and> S B \<longrightarrow> (\<exists>C. S C \<and> A \<subseteq> C \<and> B \<subseteq> C)"
definition directed_rel :: "'a Set \<Rightarrow> 'a Set Set \<Rightarrow> bool" ("directed\<^sup>_")
  where "directed\<^sup>U S \<equiv> \<forall>A B. S A \<and> S B \<longrightarrow> (\<exists>C. S C \<and> A \<subseteq>\<^sup>U C \<and> B \<subseteq>\<^sup>U C)"

(* Every maximal element of a directed set is a greatest element*)
lemma directedMaxGreatest: "directed A \<Longrightarrow> \<forall>B. maximal A B id \<longrightarrow>  greatest A B id"
  by (smt (verit, del_insts) directed_def greatest_def id_apply maximal_def)

(* A particular sort of directed set is a chain: *)
definition chain :: "'a Set Set \<Rightarrow> bool"
  where "chain C \<equiv> \<forall>A. \<forall>B. C A \<longrightarrow> C B \<longrightarrow> (A \<subseteq> B \<or> B \<subseteq> A)"
definition chain_rel :: "'a Set \<Rightarrow> 'a Set Set \<Rightarrow> bool" ("chain\<^sup>_")
  where "chain\<^sup>U C \<equiv> \<forall>A. \<forall>B. C A \<longrightarrow> C B \<longrightarrow> (A \<subseteq>\<^sup>U B \<or> B \<subseteq>\<^sup>U A)"
lemma chain_rel_impl: \<open>chain C \<Longrightarrow> chain\<^sup>U C\<close> by (metis (full_types) chain_rel_def misc.chain_def)

lemma chainDirected: "chain S \<longrightarrow> directed S" by (smt (verit, ccfv_SIG) directed_def chain_def)
lemma chainDirected_rel: "chain\<^sup>U S \<longrightarrow> directed\<^sup>U S" by (smt (verit, best) chain_rel_def directed_rel_def)
lemma "directed S \<longrightarrow> chain S"  oops (* counterexample found, as expected*)
lemma "directed\<^sup>U S \<longrightarrow> chain\<^sup>U S"  oops (* counterexample found, as expected*)

(* A is called directed-complete (aka. dcpo) if every subset that is directed has a supremum in A*)
definition omegacomplete ("\<omega>-cpo _")    where "\<omega>-cpo A \<equiv> \<forall>C. C \<subseteq> A \<and>  chain C  \<longrightarrow>  A(\<^bold>\<Or>C)"
definition omegacomplete_rel ("\<omega>-cpo\<^sup>_ _")    where "\<omega>-cpo\<^sup>U A \<equiv> \<forall>C. C \<subseteq> A \<and>  chain\<^sup>U C  \<longrightarrow>  A(\<^bold>\<Or>C \<inter> U)"
(* A is called \<omega>-complete (aka. \<omega>-cpo) if every subset that is a chain has a supremum in A*)
definition directedcomplete ("dcpo _") where "dcpo A \<equiv> \<forall>D. D \<subseteq> A \<and> directed D \<longrightarrow> A(\<^bold>\<Or>D)"
definition directedcomplete_rel ("dcpo\<^sup>_ _") where "dcpo\<^sup>U A \<equiv> \<forall>D. D \<subseteq> A \<and> directed\<^sup>U D \<longrightarrow> A(\<^bold>\<Or>D \<inter> U)"

(* Clearly, dcpos are also \<omega>-cpos (but not viceversa)*)
lemma dcpo_\<omega>: "dcpo A \<longrightarrow> \<omega>-cpo A" by (simp add: chainDirected directedcomplete_def omegacomplete_def)
lemma dcpo_\<omega>_rel: "dcpo\<^sup>U A \<longrightarrow> \<omega>-cpo\<^sup>U A" by (simp add: chainDirected_rel directedcomplete_rel_def omegacomplete_rel_def)
lemma "\<omega>-cpo A \<longrightarrow> dcpo A" (*nitpick*) oops (* counterexamples are infinite*)
lemma "\<omega>-cpo\<^sup>U A \<longrightarrow> dcpo\<^sup>U A" (*nitpick*) oops (* counterexamples are infinite*)

definition allChainsHaveUB 
  where "allChainsHaveUB A \<equiv> \<forall>C. C \<subseteq> A \<longrightarrow> chain C \<longrightarrow> (\<exists>X. A X \<and> UB C X)"
definition allChainsHaveUB_rel ("allChainsHaveUB\<^sup>_")
  where "allChainsHaveUB\<^sup>U A \<equiv> \<forall>C. C \<subseteq> A \<and> chain\<^sup>U C \<longrightarrow> (\<exists>X. A X \<and> UB\<^sup>U C X)"

lemma omegaCompleteUB: "\<omega>-cpo A \<Longrightarrow> allChainsHaveUB A" by (smt (verit, best) chains_def allChainsHaveUB_def least_def omegacomplete_def sup_char)
lemma omegaCompleteUB_rel: "\<omega>-cpo\<^sup>U A \<Longrightarrow> allChainsHaveUB\<^sup>U A" by (smt (verit, best) allChainsHaveUB_rel_def omegacomplete_rel_def supremum_def upper_bound_rel_def)

end
