# Formalization of Argumentation Frameworks

In this folder, an encoding of Dung-style abstract argumentation frameworks (AFs) into higher-order logic (HOL)
(aka. extensional type theory) is presented.
Developed by David Fuenmayor and Alexander Steen in the AuReLeE project funded by the Luxembourg National Research Fund (FNR CORE C20/IS/14616644),
originally published at https://github.com/aureleeNet/formalizations .

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
├── README.md                   --- This README file
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
