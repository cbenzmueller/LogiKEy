# LogiKEy — Logic and Knowledge Engineering

**Website: [logikey.org](https://logikey.org)**

**LogiKEy** is a logic-pluralistic framework and methodology for knowledge representation and reasoning, with a particular focus on normative reasoning, ethical & legal AI, computational metaphysics, and expressive classical and non-classical logics and their combinations. Its unifying idea: instead of building a bespoke prover for every object logic, the object logic is **semantically embedded** in classical **higher-order logic (HOL)**, so that existing interactive and automated HOL provers and (counter-)model finders — Isabelle/HOL, LEO-II, Leo-III, Sledgehammer, Nitpick, and others — are reused for reasoning in and about the embedded logics.

This repository is the **LogiKEy workbench**: the Isabelle/HOL theory files and datasets accompanying the LogiKEy publications, together with course and tutorial material. The [landing page](https://logikey.org) gives a guided overview with a curated reference list.

## Read first

- C. Benzmüller, X. Parent, L. van der Torre: *Designing Normative Theories for Ethical and Legal Reasoning: LogiKEy Framework, Methodology, and Tool Support.* Artificial Intelligence 287 (2020). [doi:10.1016/j.artint.2020.103348](https://doi.org/10.1016/j.artint.2020.103348) · [arXiv:1903.10187](https://arxiv.org/abs/1903.10187)
- C. Benzmüller, A. Farjami, D. Fuenmayor, P. Meder, X. Parent, A. Steen, L. van der Torre, V. Zahoransky: *LogiKEy Workbench (Isabelle/HOL dataset).* Data in Brief 33 (2020). [doi:10.1016/j.dib.2020.106409](https://doi.org/10.1016/j.dib.2020.106409) · [data](2020-DataInBrief-Data/)
- C. Benzmüller: *Universal (Meta-)Logical Reasoning: Recent Successes.* Science of Computer Programming 172 (2019). [doi:10.1016/j.scico.2018.10.008](https://doi.org/10.1016/j.scico.2018.10.008)
- C. Benzmüller, D. Fuenmayor, B. Lomfeld: *Modelling Value-oriented Legal Reasoning in LogiKEy.* Logics 2(1) (2024). [doi:10.3390/logics2010003](https://doi.org/10.3390/logics2010003) · [sources](Preference-Logics/EncodingLegalBalancing/)
- C. Benzmüller: *Faithful Logic Embeddings in HOL — Deep and Shallow.* CADE-30, LNCS 15943, Springer (2025). [doi:10.1007/978-3-031-99984-0_16](https://doi.org/10.1007/978-3-031-99984-0_16) · [arXiv:2502.19311](https://arxiv.org/abs/2502.19311)
- C. Benzmüller, D. Kirchner, L. Pasetto: *Many Logics, One Methodology: A Plea for Logical Pluralism in Formalised Reasoning.* Preprint (2026). [arXiv:2605.27246](https://arxiv.org/abs/2605.27246)

## Repository structure (selection)

| Folder | Content |
|---|---|
| [`2020-DataInBrief-Data/`](2020-DataInBrief-Data) | LogiKEy workbench dataset (deontic logics, logic combinations, examples) |
| [`Deontic-Logics/`](Deontic-Logics) | SDL, dyadic deontic logics (Åqvist's E, DDL cube), Input/Output logic, Gewirth case study |
| [`Preference-Logics/`](Preference-Logics) | Encoding legal balancing; value-oriented legal reasoning |
| [`Public-Announcement-Logic/`](Public-Announcement-Logic) | PAL with relativized common knowledge; wise men puzzle |
| [`LRK/`](LRK) | A dynamic logic of the Right to Know |
| [`Computational-Metaphysics/`](Computational-Metaphysics) | Gödel's/Scott's ontological argument variants (IJCAI 2016, KR 2020, BSL 2020) |
| [`Maths-Foundations/`](Maths-Foundations) | Free logic and axiomatic category theory (JAR 2020) |
| [`Fatio/`](Fatio) | Fatio protocol for multi-agent argumentation |
| [`Nitpick2TikZ/`](Nitpick2TikZ) | Visualizing Nitpick's Kripke models |
| [`2025-ICAIL-Data/`](2025-ICAIL-Data) | Logical modalities in the European AI Act (ICAIL 2025) |
| [`2026-AAMAS-Data/`](2026-AAMAS-Data) | Formalizing mental privacy (AAMAS 2026) |
| [`CoursesAndTutorials/`](CoursesAndTutorials) | Teaching material, incl. the [ESSLLI 2026 LogiKEy course](https://logikey.org/CoursesAndTutorials/2026-ESSLLI/) |

Related Isabelle/HOL datasets are also published in the Archive of Formal Proofs, e.g. [PAL](https://www.isa-afp.org/entries/PAL.html), [CondNormReasHOL](https://www.isa-afp.org/entries/CondNormReasHOL.html), [FaithfulPMLinHOL](https://www.isa-afp.org/entries/FaithfulPMLinHOL.html), [MSOinHOL](https://isa-afp.org/entries/MSOinHOL.html), [Notes_On_Goedels_Ontological_Argument](https://www.isa-afp.org/entries/Notes_On_Goedels_Ontological_Argument.html), [Boolos_Curious_Inference_Automated](https://www.isa-afp.org/entries/Boolos_Curious_Inference_Automated.html).

## Stable links

Paths in this repository (e.g. `logikey.org/tree/master/…`) are cited in published papers and are kept stable; `logikey.org` forwards any such deep link to the corresponding location in this repository.

## Citation

```bibtex
@article{LogiKEy,
  author  = {Christoph Benzm{\"u}ller and Xavier Parent and Leendert van der Torre},
  title   = {Designing Normative Theories for Ethical and Legal Reasoning:
             {LogiKEy} Framework, Methodology, and Tool Support},
  journal = {Artificial Intelligence},
  volume  = {287},
  pages   = {103348},
  year    = {2020},
  doi     = {10.1016/j.artint.2020.103348},
}
```

Maintained by [Christoph Benzmüller](https://christoph-benzmueller.de) and collaborators.
