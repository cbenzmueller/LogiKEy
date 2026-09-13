# Implicit disagreement in Isabelle/HOL

This is the Isabelle/HOL encoding of the paper *When We Disagree to Agree: An Abstract Argumentation Account of Implicit Disagreement in Legal Reasoning*.

## Mapping to the paper

| Paper | Isabelle representation | Location |
|---|---|---|
| Framework | Existing argument predicate `U :: 'a Set` and `att :: 'a Rel` | Imported library; no replacement record |
| Extension semantics (defence, complete, grounded, preferred) | `defends_rel`, `extensions.completeExt`, `extensions.groundedExt`, `extensions.preferredExt` | Imported library |
| Conclusion map | Parameter `Con :: 'a => 'c` | New predicates, polymorphic in conclusion type |
| Inference relations (credulous, shared conclusion, shared argument) | `credulous_conclusion`, `shared_conclusion`, `shared_argument` | `ID_Inference.thy` |
| Agents | `is_agent U att A r`, with `r = induced_att att A` | `ID_Frameworks.thy` |
| Coalition | `coalition A B`, abbreviation for imported union; `coalition_att` | `ID_Frameworks.thy` |
| Agreement (agrees that / agrees because) | `agrees_that`, `agrees_because`, aliases for the corresponding inference relations | `ID_Inference.thy` |
| Proximal explanation | `proximal_explanation U Con p a` | `ID_Inference.thy` |
| Explanation | `explanation_support` for conditions 1–2; `explanation` uses imported `minimal` | `ID_Explanations.thy` |
| Shared-explanation inference / strong agreement because | `shared_explanation`; alias `strongly_agrees_because` | `ID_Explanations.thy` |
| Disagreement predicates (ordinary, proximal, distal) | `disagrees_that`, `proximal_disagreement`, `distal_disagreement` | `ID_Disagreement.thy` |
| Actual implicit disagreement | `proximal_implicit_disagreement`, `distal_implicit_disagreement`, coalition-evaluated aliases of the disagreement predicates | `ID_Disagreement.thy` |
| Potential implicit disagreement | `potential_proximal_disagreement A B att Con p`, `potential_distal_disagreement A B att Con p` | `ID_Disagreement.thy` |
| Deletion and weak spots | `remove_argument`, `remove_att`, `weak_spot` | `ID_Frameworks.thy`, `ID_Disagreement.thy` |
| Informal antagonist passage | `antagonist`, with the explicit convention described below | `ID_Disagreement.thy` |
| Shared-explanation / ideal-semantics correspondence | `shared_explanation_iff_idealset` (finite `U`) | `ID_Explanations.thy` |

## Interpretation choices

Sets are characteristic predicates, using the library's `'a Set` type and inclusion/union operations. An agent can have an empty argument universe even though the ambient HOL type is nonempty. The attack relation of an agent or coalition is induced by its arguments. The proved `*_induced` lemmas justify using an ambient attack relation with the smaller universe when evaluating the relative semantics.

The inference predicates range over preferred extensions, not stable extensions. `shared_conclusion` means that **each extension contains some argument** with the conclusion; `shared_argument` means that **one argument occurs in every extension**. They cannot be identified with each other or with the existing argument-level labelling acceptance predicates. Witness arguments are explicitly required to belong to `U`, since the imported extension predicates ignore membership outside that universe.

The conclusion type is arbitrary and no entailment on conclusions is assumed. In particular, an argument concluding a conjunction does not automatically conclude either conjunct. Multiple arguments may have the same conclusion. A proximal explanation is therefore a relation, not a single-valued choice function.

The explanation definition is encoded literally: an explanation is an inclusion-minimal subset of the framework that contains a concluder and defends all its own arguments. Defence is evaluated against attackers in the entire current framework, not just in the explanation's induced subgraph. Conflict-freeness is not added to that definition. A self-attacking singleton illustrates this distinction. Nevertheless, any explanation shared by every preferred extension is admissible; the theory proves this using the imported preferred-extension existence and conflict-freeness results.

All definitions work without assuming finitely many arguments or finitely many preferred extensions. This generalizes the paper's finite indexing by quantification; it does not add an assertion that a minimal explanation always exists in an infinite framework.

Potential disagreement retains the two agents as separate parameters because their individual commitments matter. Actual implicit disagreement is exactly the corresponding proximal/distal disagreement of their coalition and is only abbreviated, avoiding duplicate definitions.

A weak spot must turn shared-conclusion acceptance into ordinary disagreement after deletion: some preferred extension must still support the conclusion, while another does not. Merely removing its sole concluder is insufficient. The paper informally calls an argument an antagonist when its removal strengthens agreement. Here that is made precise as a present argument whose removal turns distal disagreement into shared-explanation agreement; this convention is explicitly distinguished from the numbered definitions.

`ID_Examples.thy` tests the quantifier distinction, coalition edges, the non-conflict-free explanation definition, and the displayed six-argument graph.

