# AFP-readiness checklist

Status of the `ImplicitDisagreement` development against the standards of the
[Archive of Formal Proofs](https://www.isa-afp.org/). This is a post-paper
robustness/quality effort, not required for the JURIX artifact. Items are grouped
by how strongly they block an AFP submission.

Audit date: 2026-09-13 (Isabelle2025-2).

## Already in good shape

- No `sorry` and no `apply`-scripts anywhere in `ID_*.thy`: all proofs are
  structured Isar.
- Substantial explanatory prose in `text` blocks, cross-referencing the paper.
- Per-theory `section` headings; the generated document has a populated table of
  contents.
- The session builds cleanly (`build.sh`), and is verified cross-platform in CI.

## Blocking (must resolve before any AFP submission)

- [ ] **`AA_Fixed` is a vendored, modified copy of a third-party development.**
  It is a corrected fork of David Fuenmayor and Alexander Steen's argumentation
  formalization (originally at <https://github.com/aureleeNet/formalizations>,
  LNGAI 2021). AFP does not accept bundling an edited copy of someone else's work
  inside an entry. Resolve by one of:
  - upstreaming the corrections and *depending* on the authors' entry, or
  - submitting `AA_Fixed` as its own AFP entry, with the original authors
    credited/co-authoring, and this development depending on it.
- [ ] **`AA_Fixed` is not itself AFP-clean.** It currently contains ~53 leftover
  `sledgehammer`/`oops`/`nitpick` occurrences, ~78 `smt` calls, and builds with
  `document = false`. It would need the same hygiene pass as below.

## Should-fix (standard AFP reviewer requests)

- [ ] **Replace `smt` with reproducible methods.** Two `smt (verit)` calls in
  `ID_*` (`ID_Disagreement.thy`, `ID_Explanations.thy`), ~78 in `AA_Fixed`.
  AFP prefers `metis`/`meson`/structured proofs so the build does not depend on a
  specific SMT solver's behaviour.
- [ ] **Remove the `nitpick … oops` regression lemma** in `ID_Explanations.thy`
  (`shared_explanation_iff_idealset_nitpick`) or gate it out of the AFP build:
  it runs the model finder on every build and leaves an `oops`. The corresponding
  positive result (`shared_explanation_iff_idealset`) is already proved.
- [ ] **Add standard theory headers.** None of the five theories has a
  title/author/date/license header block. AFP entries carry these plus an
  `AFP/thys/<Entry>/` metadata record.
- [ ] **Add a license.** AFP requires BSD-3-Clause or LGPL; add the license file
  and reference it from the headers.
- [ ] **Reshape `ROOT` for AFP.** Declare the session under `chapter AFP`, use the
  AFP entry name, and add the metadata entry. Reconsider the tuning options
  `parallel_proofs = 0` and the enlarged `timeout`: these are fragility
  workarounds (see below) rather than intended configuration.

## Polish (reviewers will note, not usually blocking)

- [ ] **Line length.** Longest lines: `ID_Inference` 142, `ID_Explanations` 140,
  `ID_Frameworks` 123, `ID_Examples` 116, `ID_Disagreement` 101. AFP's soft target
  is ~80–100 columns; wrap the long statements/proof lines.
- [ ] **Proof robustness.** `parallel_proofs = 0` was needed because a `blast`
  step diverged under parallel proofs (the ideal-set correspondence uses an
  explicit `[OF …]` instantiation to avoid this). Prefer proofs that are robust
  under the default settings so the tuning options can be dropped.
- [ ] **`metis` with long fact lists / `(lifting)`.** Several one-liners
  (e.g. in `ID_Examples.thy`) lean on `metis` with many named facts; consider
  tightening to smaller, more transparent steps where practical.

## Fixed in this pass (2026-09-13)

- [x] Removed a stray `sledgehammer` left between the statement and proof of
  `fresh_attacker_complete` in `ID_Frameworks.thy` (ran an external prover search
  on every build).
- [x] Stripped trailing whitespace from `ID_Explanations`, `ID_Disagreement`,
  `ID_Examples`, `ID_Inference`.
