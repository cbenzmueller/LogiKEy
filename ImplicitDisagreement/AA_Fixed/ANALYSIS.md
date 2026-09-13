# Structure and semantics of the formalization

The files formalize abstract argumentation frameworks in Isabelle/HOL: arguments are values, attacks are a binary relation, extensions are predicates, and labellings assign `In`, `Out`, or `Undec` to arguments. The changes to the original foundations, skeptical-acceptance definition, and example queries are recorded in [CHANGES.md](CHANGES.md).

The reference is David Fuenmayor and Alexander Steen, *A Flexible Approach to Argumentation Framework Analysis using Theorem Proving*, LNGAI 2021, proceedings pp. 18–32. The [publisher's proceedings](https://www.collegepublications.co.uk/downloads/LNGAI00001.pdf#page=27) provide the paper. Its whole-type encoding corresponds most closely to `simplified/`. The main development adds an explicit argument universe. The paper leaves a general translation-faithfulness proof to future work; the repairs do not claim to supply that separate result.

## How to read the theories

| Files | Role |
|---|---|
| `misc.thy`, `Zorn-lemma.thy` | Predicate-set operations, relative orders, fixed points, and maximal-element existence. |
| `base.thy` | Attack images, defence, label datatype, acceptance, and model-generation helpers. |
| `extensions.thy`, `labellings.thy` | Definitions of the argumentation semantics. |
| `ext-properties.thy`, `lab-properties.thy` | Properties and existence results within each representation. |
| `ext-relationships.thy`, `lab-relationships.thy` | Implications and alternative characterizations between semantics. |
| `correspondence.thy` | Conversion between extensions and labellings. |
| `adequacy.thy` | Representative Dung-style metatheorems. |
| `simplified/` | Parallel development using the entire HOL type as the argument universe; includes the three finite examples. |
| `regression-checks.thy` | Checks for the repaired defects and an audit of mathematical proof dependencies. |

An extension `E` is represented by a function to Boolean values: `E a` means that argument `a` belongs to the extension. `att a b` means that `a` attacks `b`. An argument is defended by `E` if each of its attackers is attacked by some member of `E`.

| Semantics | Meaning |
|---|---|
| Conflict-free | No two members attack one another, including self-attacks. |
| Admissible | Conflict-free and defends every member. |
| Complete | Admissible and includes every argument it defends. |
| Grounded | The least complete extension under inclusion. |
| Preferred | An inclusion-maximal admissible extension, equivalently an inclusion-maximal complete extension. |
| Stable | Conflict-free and attacks every argument outside the extension. |
| Semi-stable | Complete, with inclusion-maximal union of accepted and attacked arguments. |
| Stage | Conflict-free, with inclusion-maximal union of accepted and attacked arguments. |
| Ideal | The greatest admissible extension contained in every preferred extension. |

“Maximal” means that no eligible strict superset exists. It does not mean maximum cardinality. “Least” means contained in every eligible set. These distinctions are encoded in the order definitions.

For labellings, legally `In` means all attackers are `Out`; legally `Out` means some attacker is `In`; legally `Undec` means neither condition holds. The printed `legallyOut` formula on proceedings p. 24 contains an implication under an existential. The prose and appendix code require conjunction, as the implementation does.

`Lab2Ext` extracts the `In` arguments. `Ext2Lab` labels extension members `In`, their targets `Out`, and the remainder `Undec`. Complete labellings are determined by their `In` sets. Admissible labellings need not be: each four-argument example has five admissible extensions but seven admissible labellings.

The explicit-universe development compares predicates and labellings on that universe. They may differ elsewhere without representing different solutions of the framework. The simplified development uses the entire type, which HOL requires to be nonempty but does not require to be finite. The example datatypes are finite and exhaustive.

## Why the repairs matter

The former Zorn bridges confused relative inclusion with global inclusion and were admitted using `sorry`. With an empty relative universe, every inclusion comparison is vacuous; that cannot establish a global upper bound for the chain of finite prefixes of the natural numbers. The corrected file proves relative Zorn through restricted predicates. The regression suite proves the old bridge's counterexample, so it cannot silently return as a valid foundation.

Skeptical acceptance now requires an argument to be `In` in **every** semantic labelling. The original definition ignored labellings with no `In` arguments. Consequently it incorrectly accepted a self-attacking argument whose only complete labelling is `Undec`. The regression suite checks that this argument is neither credulously nor skeptically accepted, while an unattacked argument is skeptically accepted. With no semantic labellings, the universal skeptical condition remains vacuously true; skeptical-to-credulous implication therefore requires existence of a semantic labelling.

The repaired example queries refer to the intended semantics and constructors. Their exact finite domains avoid undersized Nitpick scopes. Optional cardinality displays were removed because their auxiliary list/natural-number encoding produced potentially spurious models; the queries still characterize the entire solution family using `findFor'`. The impossible request for more than two `In` arguments in Figure 4 is now a proved upper bound.

## Reading the examples and evidence

| Example | Complete extensions | Grounded / ideal | Preferred / semi-stable | Stable |
|---|---|---|---|---|
| Figure 4: A attacks B, B attacks C, C and D attack each other | {A}, {A,C}, {A,D} | {A} | {A,C}, {A,D} | {A,C}, {A,D} |
| Figure 5: A and B attack each other and C; C attacks D | ∅, {A,D}, {B,D} | ∅ | {A,D}, {B,D} | {A,D}, {B,D} |
| Figure 6: directed three-cycle | ∅ | ∅ | ∅ | none |

Here `∅` denotes one extension containing no arguments; “none” denotes no extension at all. For the three-cycle, the complete labelling assigns `Undec` everywhere. The example theory also proves the concrete ideal labellings.

Proofs closed with `by` or `qed` establish theorems, subject to their assumptions and proof dependencies. `oops` discards a statement. It is intentional after a model-generation query or false converse, and also marks remaining open research conjectures. A Nitpick model is evidence about a concrete finite framework; failure to find a countermodel is not a proof for arbitrary frameworks. Semi-stable existence is proved with a finiteness assumption. Build instructions and the scope of the proof-dependency audit are documented in [README.md](README.md#verification).
