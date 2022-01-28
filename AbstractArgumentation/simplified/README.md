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
