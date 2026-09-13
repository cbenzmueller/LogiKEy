# Simplified Formalization of Argumentation Frameworks

In this folder, a simplified encoding of Dung-style abstract argumentation frameworks (AFs) into higher-order logic (HOL)
(aka. extensional type theory) is presented.

## File structure

```
.
├── correspondence-simpl.thy    --- Correspondences between labellings and extensions
├── extensions-simpl.thy        --- Extension-based argumentation semantics
├── ext-simpl-properties.thy    --- Proves some properties of extensions and refutes others
├── ext-simpl-relationships.thy --- Proves inclusion relationships among extensions
├── labellings-simpl.thy        --- Labelling-based argumentation semantics
├── lab-simpl-properties.thy    --- Proves some properties of labellings and refutes others
├── lab-simpl-relationships.thy --- Proves inclusion relationships among labellings
├── model-generation.thy        --- Generation of extensions and labellings using Nitpick
└── README.md                   --- This README file
```

## Repair notes (September 2026)

This directory uses the whole HOL type as its argument universe. The semantic predicates and examples now
refer to the intended constants. The ideal extension completeness argument uses
ordinary reconstructed proofs, and ideal semantics has extension/labelling
correspondence proofs. The concrete ideal labellings for all three supplied
figures are proved in `model-generation.thy`.

`semistable_exist_finite` explicitly restricts the argument type to `finite`.
Semi-stable labellings need not exist over arbitrary infinite frameworks.

Nitpick queries followed by `oops` are model searches, not exported theorems.
The Figure 4 theory proves that an admissible labelling has at most two `In`
arguments. Proof obligations closed by `by` or `qed` are checked by the session
build. The remaining `TODO`/`oops` conjectures about fixed-point and
complete-labelling characterizations are not proved results. See
[README.md](../README.md#verification) for build instructions and the proof-audit scope.
