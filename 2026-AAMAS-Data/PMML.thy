section ‹Propositional Multi-Modal Logic in HOL›
text ‹›

theory PMML imports Main begin  
nitpick_params[user_axioms=true,assms=true,expect=genuine, show_all, format=2]

text ‹Type i is associated with possible worlds›
typedecl i 
typedecl ag
type_synonym σ = "i⇒bool" (*Type of world domains *)
type_synonym γ = "i⇒i⇒bool" (* Type of accessibility relations between worlds *)
type_synonym 𝒩 = "i ⇒ (σ ⇒ bool)"
type_synonym ρ = "γ⇒bool" (* Type of groups of agents *)

text ‹Some useful relations (for constraining accessibility relations)›
definition reflexive::"γ⇒bool" 
  where "reflexive R ≡ ∀x. R x x"
definition symmetric::"γ⇒bool" 
  where "symmetric R ≡ ∀x y. R x y ⟶ R y x"
definition serial::"γ⇒bool"
  where "serial R ≡ ∀x. ∃y. R x y"
definition transitive::"γ⇒bool" 
  where "transitive R ≡ ∀x y z. R x y ∧ R y z ⟶ R x z"
definition euclidean::"γ⇒bool" 
  where "euclidean R ≡ ∀x y z. R x y ∧ R x z ⟶ R y z"
abbreviation(input) intersection_rel::"γ⇒γ⇒γ" (infixr"❙∩"51) 
  where "intersection_rel R Q ≡ λu v. R u v ∧ Q u v"
definition union_rel::"γ⇒γ⇒γ" 
  where "union_rel R Q ≡ λu v. R u v ∨ Q u v"
definition sub_rel::"γ⇒γ⇒bool" 
  where "sub_rel R Q ≡ ∀u v. R u v ⟶ Q u v"
definition inverse_rel::"γ⇒γ" 
  where "inverse_rel R ≡ λu v. R v u"
definition big_union_rel::"ρ⇒γ" 
  where "big_union_rel X ≡ λu v. ∃R. (X R) ∧ (R u v)"
definition big_intersection_rel::"ρ⇒γ"
  where "big_intersection_rel X ≡ λu v. ∀R. (X R) ⟶ (R u v)"
text ‹In HOL the transitive closure of a relation can be defined in a single line.›
definition tc::"γ⇒γ" 
  where "tc R ≡ λx y.∀Q. transitive Q ⟶ (sub_rel R Q ⟶ Q x y)"

abbreviation(input) cartesian_product :: "σ ⇒ σ ⇒ γ" where
  "cartesian_product V W ≡ (λx y. ((V x)∧(W y)))"


(* SEMANTICS *)
text ‹Logical connectives›

definition matom::"(i⇒bool)⇒σ" ("⇧A_"[79]80) 
  where "⇧Apred ≡ λw. pred w"
definition mtop::"σ" ("❙⊤") 
  where "❙⊤ ≡ λw. True" 
definition mneg::"σ ⇒ σ" ("❙¬_"[52]53) 
  where "❙¬φ ≡ λw. ¬(φ w)" 
definition mand::"σ⇒σ⇒σ" (infixr"❙∧"51) 
  where "φ❙∧ψ ≡ λw. (φ w) ∧ (ψ w)"   
definition mor::"σ⇒σ⇒σ" (infixr"❙∨"50) 
  where "φ❙∨ψ ≡ λw. (φ w) ∨ (ψ w)"  
definition mimp::"σ⇒σ⇒σ" (infixr"❙→"49)
  where "φ❙→ψ ≡ λw. (φ w) ⟶ (ψ w)" 
definition mequ::"σ⇒σ⇒σ" (infixr"❙↔"48) 
  where "φ❙↔ψ ≡ λw. (φ w) ⟷ (ψ w)"

(*box modality *)
consts rbox::"γ" 
definition mbox :: "σ⇒σ" ("❙□ _") where "❙□ φ ≡ (λw. ∀v. rbox w v ⟶ φ v)"
abbreviation(input) mdia :: "σ⇒σ" ("❙◇ _") where "❙◇ φ ≡ (❙¬❙□❙¬ φ)" 
(* abbreviation(input) mdia :: "σ⇒σ" ("❙◇ _") where "❙◇ φ ≡ (λw. ∃v. rbox w v ∧ φ v)"   *)
(* equivalence relation *)
axiomatization where
  AxiomS5_box: "reflexive (rbox) ∧ symmetric (rbox) ∧ transitive (rbox)" 
(* AxiomKT45_box: "reflexive (rbox) ∧ transitive (rbox) ∧ euclidean (rbox)" *)


(* a neighborhood function for each agent *)
consts ag_n::"ag⇒𝒩"
(* For every w ∈ W, each set in the neighborhood N(w) includes w *)
axiomatization where
  Reflexive_n: "∀agent::ag. ∀w::i. ∀X::σ. ((((ag_n agent) w) X) ⟶ (X w) )"
definition mstit::"ag⇒σ⇒σ" ("❙E_ _") 
  where "❙E x φ ≡ λw. (((ag_n x) w) φ)"

(* deontic modality *)
consts ag_o::"ag⇒ag⇒γ"
definition mobl::"ag⇒ag⇒σ⇒σ" ("❙O[_→_] _") 
  where "❙O[x→y] φ ≡ λw.∀v. ((ag_o x y) w v ⟶ φ v)"
abbreviation(input) mper :: "ag⇒ag⇒σ⇒σ" ("❙P[_→_] _")
  where "❙P[x→y] φ ≡ (❙¬❙O[x→y] ❙¬φ)"  
(* serial relation *)
axiomatization where
  AxiomKD_obl: "∀x y. serial (ag_o x y)"

(* print_theorems *)

text ‹Global validity of formulas›
abbreviation(input) mvalid::"σ ⇒ bool" ("⌊_⌋"[47]48) 
  where "⌊φ⌋ ≡ ∀w. φ w"

abbreviation(input) mtrue_world::"σ ⇒ i ⇒ bool" ("⌊_⌋_"[47]48) 
  where "⌊φ⌋w ≡  φ w"

(* this is local, corresponds to implication *)
abbreviation(input) mconsequence :: "σ ⇒ σ ⇒ bool" (infixl "⊨" 10) where "ψ ⊨ φ ≡ ∀w. ( (ψ w) ⟶ φ w)"

text ‹Introducing "Defs" as the set of the above definitions; useful for convenient unfolding.›
(*
named_theorems Defs
declare reflexive_def[Defs] symmetric_def[Defs] transitive_def[Defs] 
  euclidean_def[Defs] intersection_rel_def[Defs] union_rel_def[Defs] 
  sub_rel_def[Defs] inverse_rel_def[Defs] big_union_rel_def[Defs] 
  big_intersection_rel_def[Defs] tc_def[Defs]
*)
named_theorems HOMML_Defs
declare 
matom_def[HOMML_Defs]
mtop_def[HOMML_Defs]
mneg_def[HOMML_Defs]
mand_def[HOMML_Defs]
mor_def[HOMML_Defs]
mimp_def[HOMML_Defs]
mequ_def[HOMML_Defs]
mbox_def[HOMML_Defs]
mstit_def[HOMML_Defs]
mobl_def[HOMML_Defs]


text ‹Consistency: nitpick reports a model.›
lemma True nitpick[satisfy] oops (* model found *)

end
