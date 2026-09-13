# Formalization of Argumentation Frameworks

This development targets Isabelle2025. [CHANGES.md](CHANGES.md) records the corrections to the original formalization; [ANALYSIS.md](ANALYSIS.md) explains the definitions, metatheorems, and examples.

In this folder, an encoding of Dung-style abstract argumentation frameworks (AFs) into higher-order logic (HOL)
(aka. extensional type theory) is presented.
Developed by David Fuenmayor and Alexander Steen in the AuReLeE project funded by the Luxembourg National Research Fund (FNR CORE C20/IS/14616644),
originally published at https://github.com/aureleeNet/formalizations .

The main theories use an explicit argument universe. The `simplified/` theories use the whole HOL type as the universe. Both represent sets as predicates and labellings as functions into `In`, `Out`, and `Undec`.

## File structure

```
.
├── adequacy.thy                --- Proves some exemplary theorems to demonstrate the adequacy of the encoding
├── base.thy                    --- Basic definitions on arguments, extensions, labellings, etc.
├── correspondence.thy          --- Correspondences between labellings and extensions
├── extensions.thy              --- Extension-based argumentation semantics
├── ext-properties.thy          --- Proves some properties of extensions and refutes others
├── ext-relationships.thy       --- Proves inclusion relationships among extensions
├── labellings.thy              --- Labelling-based argumentation semantics
├── lab-properties.thy          --- Proves some properties of labellings and refutes others
├── lab-relationships.thy       --- Proves inclusion relationships among labellings
├── misc.thy                    --- Miscellaneous basic definition (sets, relations, orderings, etc.)
├── regression-checks.thy       --- Regression theorems and an audit of mathematical proof dependencies
├── ROOT                        --- Isabelle session containing all 20 theories
├── simplified                  --- Contains simplified AF definitions (analogous naming scheme)
│   ├── correspondence-simpl.thy
│   ├── extensions-simpl.thy
│   ├── ext-simpl-properties.thy
│   ├── ext-simpl-relationships.thy
│   ├── labellings-simpl.thy
│   ├── lab-simpl-properties.thy
│   ├── lab-simpl-relationships.thy
│   └── model-generation.thy    --- Generation of extensions and labellings using Nitpick
└── Zorn-lemma.thy              --- Useful lemmas concerning orderings (incl. Zorn's)
```

## Building

With Isabelle2025 on `PATH`, run from this directory:

```sh
isabelle build -D .
```

To inspect failed-build diagnostics:

```sh
isabelle build_log -H Error AA_Fixed
```

## Verification

[ROOT](ROOT) includes all 20 theories and sets `quick_and_dirty=false`. [regression-checks.thy](regression-checks.thy) checks skeptical acceptance for self-attacking and unattacked arguments and proves counterexamples to both removed relative/global Zorn bridges.

The same theory uses `Thm_Deps.all_oracles` to inspect the full proof ancestry of project mathematical facts and fails the build on any oracle dependency. Eight explicitly named Quickcheck support collections are excluded as audit roots: the generated `full_exhaustive_*.simps` and `narrowing_*.simps` collections for `base.Label` and the three example `Arg` datatypes. Mathematical results that depend on those equations still fail the audit. The audit output is produced on rebuilding the session.

Statements ending in `oops` are discarded experiments or open conjectures, not exported theorems. Nitpick searches provide finite examples or counterexamples; failure to find a counterexample is not a general proof. Semi-stable existence is proved under a finiteness assumption. The separate general translation-faithfulness theorem left open in the reference paper is not supplied here.
