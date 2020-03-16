theory ModalEmbedCompleteness
  imports Main

begin
declare [["syntax_ambiguity_warning" = false]]

context begin

(* ########################################################################## *)
(* utility methods: conversion from sets to precidates and vice versa.  *)
definition set_to_pred :: "'a set \<Rightarrow> ('a \<Rightarrow> bool)"
  where "set_to_pred M \<equiv> \<lambda>x. (x \<in> M)"
definition pred_to_set :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set"
  where "pred_to_set P \<equiv> {x. P x}"

lemma setPred1: "\<forall>M. x \<in> M \<longleftrightarrow> (set_to_pred M) x" unfolding set_to_pred_def by auto
lemma setPred2: "\<forall>P. P x \<longleftrightarrow> x \<in> (pred_to_set P)" unfolding pred_to_set_def by auto

definition rel_to_pred :: "'a rel \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
  where "rel_to_pred R \<equiv> \<lambda>x y. (x,y) \<in> R"
definition pred_to_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a rel"
  where "pred_to_rel P \<equiv> {(x,y) | x y. P x y}"

lemma relPred1: "\<forall>R. (x,y) \<in> R \<longleftrightarrow> (rel_to_pred R) x y" unfolding rel_to_pred_def by auto
lemma relPred2: "\<forall>P. P x y \<longleftrightarrow> (x, y) \<in> (pred_to_rel P)" unfolding pred_to_rel_def by auto
(* utility end *)
(* ########################################################################## *)

type_synonym id = string  \<comment> \<open>type of atomic propositions, here: strings\<close>
typedecl i
type_synonym acc = "i \<Rightarrow> i \<Rightarrow> bool" \<comment> \<open>accessibility relation type\<close>
type_synonym varassgn = "id \<Rightarrow> i \<Rightarrow> bool" \<comment> \<open>type of variable assignment\<close>

(* ########################################################################## *)
(* Embedding BEGIN *)
datatype fm              \<comment> \<open>type of modal logic formulas\<close>
 = Atom id ("\<langle>_\<rangle>")
 | Impl fm fm (infixr "\<^bold>\<longrightarrow>" 49)
 | Neg fm ("\<^bold>\<not> _" [52]53)
 | Box fm ("\<^bold>\<box> _" [52]53)

(* embedding function on the object logic level *)
fun embed :: "fm \<Rightarrow> acc \<Rightarrow> varassgn \<Rightarrow> (i \<Rightarrow> bool)" ("\<lceil>_\<rceil>"[50]50) 
  where 
    "\<lceil>Atom p\<rceil> = (\<lambda>r. \<lambda>g.(\<lambda>w. g p w))"
  | "\<lceil>Impl p q\<rceil> = (\<lambda>r. \<lambda>g. (\<lambda>w. (((\<lceil>p\<rceil>) r g) w) \<longrightarrow> (((\<lceil>q\<rceil>) r g) w)))"
  | "\<lceil>Neg p\<rceil> = (\<lambda>r. \<lambda>g. (\<lambda>w. \<not> (((\<lceil>p\<rceil>) r g) w)))" 
  | "\<lceil>Box p\<rceil> = (\<lambda>r. \<lambda>g. (\<lambda>w. \<forall>v. (r w v) \<longrightarrow> (((\<lceil>p\<rceil>) r g) v)))" 
                
abbreviation disj :: "fm \<Rightarrow> fm \<Rightarrow> fm" (infixr "\<^bold>\<or>" 50) 
  where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<^bold>\<not>\<phi>) \<^bold>\<longrightarrow> \<psi>"
abbreviation conj :: "fm \<Rightarrow> fm \<Rightarrow> fm" (infixr "\<^bold>\<and>" 51) 
  where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>((\<^bold>\<not>\<phi>) \<^bold>\<or> (\<^bold>\<not>\<psi>))"

definition grounding :: "(i \<Rightarrow> bool) \<Rightarrow> bool" ("\<lfloor>_\<rfloor>")
  where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> w"

(* for testing, pretty much as usual, only with explicit r and g *)
lemma "\<lfloor>((\<lceil>(p \<^bold>\<or> \<^bold>\<not>p)\<rceil>) r g)\<rfloor>" by (simp add: grounding_def)
lemma "\<lfloor>((\<lceil>(\<^bold>\<box>(p \<^bold>\<or> \<^bold>\<not>p))\<rceil>) r g)\<rfloor>" by (simp add: grounding_def)

(* Embedding END *)
(* ########################################################################## *)


(* ########################################################################## *)
(* Reference semantics BEGIN *)

datatype kripke = Kripke (\<pi>: "id \<Rightarrow> i set") (\<R>: "i rel")

fun validity_wrt_model_world :: "kripke \<Rightarrow> i \<Rightarrow> fm \<Rightarrow> bool"
  ("_,_ \<Turnstile> _" [50,50]50) where
  "(M,w \<Turnstile> (Atom x)) = (w \<in> \<pi> M x)"
| "(M,w \<Turnstile> (Impl \<phi> \<psi>)) = ((M,w \<Turnstile> \<phi>) \<longrightarrow> (M,w \<Turnstile> \<psi>))"
| "(M,w \<Turnstile> (Neg \<phi>)) = (\<not>(M,w \<Turnstile> \<phi>))"
| "(M,w \<Turnstile> (Box \<phi>)) = (\<forall>v. ((w, v) \<in> \<R> M) \<longrightarrow> (M,v \<Turnstile> \<phi>))"
(* semantics end *)

definition validity_wrt_model :: "kripke \<Rightarrow> fm \<Rightarrow> bool"
 ("_ \<Turnstile> _" [50]50) where "(M \<Turnstile> \<phi>) \<equiv> \<forall>w. M,w \<Turnstile> \<phi>"

definition valid :: "fm \<Rightarrow> bool"
 ("\<Turnstile> _" 50) where "(\<Turnstile> \<phi>) \<equiv> \<forall>M. M \<Turnstile> \<phi>"

(* consistency *)
lemma "True" nitpick[satisfy,expect=genuine] oops

(* Reference semantics END *)
(* ########################################################################## *)


(* ########################################################################## *)
(* faithfulness BEGIN *)


(* relate predicates to sets and/or relations *)
lemma eval: "\<forall>w. (embed \<phi>) r g w = ((Kripke (\<lambda>v. pred_to_set (g v)) (pred_to_rel r)), w \<Turnstile> \<phi>) "
  unfolding pred_to_set_def pred_to_rel_def by (induct \<phi>; simp_all) 

lemma eval': "\<forall>w. (embed \<phi>) (rel_to_pred r) (\<lambda>id. set_to_pred (g id)) w = ((Kripke g r), w \<Turnstile> \<phi>)"
  unfolding set_to_pred_def rel_to_pred_def by (induct \<phi>; simp_all) 

(* both directions *)
lemma soundness: "(\<forall>r g. \<lfloor>(embed \<phi>) r g\<rfloor>) \<Longrightarrow> \<Turnstile> \<phi> " 
  unfolding valid_def validity_wrt_model_def grounding_def by (metis eval' kripke.collapse)

lemma completeness: "\<Turnstile> \<phi>  \<Longrightarrow> (\<forall>r g. \<lfloor>(embed \<phi>) r g\<rfloor>) "  
  unfolding valid_def validity_wrt_model_def grounding_def by (metis eval)

(* actual faithfulness *)
theorem "\<Turnstile> \<phi> \<longleftrightarrow> (\<forall>r g. \<lfloor>(embed \<phi>) r g\<rfloor>)" using soundness completeness by auto 


(*faithfulness END *)
(* ########################################################################## *)

end

end