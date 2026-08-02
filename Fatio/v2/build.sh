#!/usr/bin/env bash
# ---------------------------------------------------------------------------
# build.sh -- verification (and optional PDF document) for the FatioFaithful
# entry. Several build versions are provided below; exactly one should be
# active, the others are kept as commented alternatives.
#
# Requirements: an Isabelle installation (Isabelle2025 or later) on the PATH,
# or pointed to via the ISABELLE environment variable, e.g.
#   ISABELLE=/opt/Isabelle2025/bin/isabelle ./build.sh
# The PDF versions additionally require LaTeX (lualatex; on Debian/Ubuntu:
#   apt install texlive-latex-base texlive-latex-recommended \
#               texlive-fonts-recommended texlive-plain-generic ).
# ---------------------------------------------------------------------------
set -euo pipefail
cd "$(dirname "$0")"

ISABELLE="${ISABELLE:-isabelle}"
DIRS="${DIRS:-}"          # extra -d session directories, if ever needed

# ---------------------------------------------------------------------------
# Version 1 (ACTIVE): verification only -- no document.
# Fastest round trip; this is what the AFP build farm effectively checks first.
# ---------------------------------------------------------------------------
# "$ISABELLE" build -v $DIRS -D .

# ---------------------------------------------------------------------------
# Version 2: verification + PDF document.
# The PDF (document.pdf) is placed in ./output together with the generated
# LaTeX sources. Note the -c: if the session heap is already up to date from a
# documentless run, Isabelle would otherwise skip document generation.
# ---------------------------------------------------------------------------
"$ISABELLE" build -c -v $DIRS -o document=pdf -o document_output="$PWD/output" -D .
echo "PDF written to: $PWD/output/document.pdf"

# ---------------------------------------------------------------------------
# Version 3: clean rebuild (invalidate the session heap first).
# Use after larger edits, or to reproduce a from-scratch AFP check.
# ---------------------------------------------------------------------------
# "$ISABELLE" build -c -v $DIRS -D .

# ---------------------------------------------------------------------------
# Version 4: clean rebuild + PDF + HTML browser info (closest to what the
# AFP publishes: theories browsable as HTML, PDF as the entry document).
# ---------------------------------------------------------------------------
# "$ISABELLE" build -c -v $DIRS -o browser_info -o document=pdf \
#     -o document_output=output -D .

# ---------------------------------------------------------------------------
# Version 5: verification with a timing/parallelism profile pinned down
# (deterministic single-threaded run; useful for timeout calibration, cf. the
# [timeout = 600] session option in ROOT).
# ---------------------------------------------------------------------------
# "$ISABELLE" build -v $DIRS -o threads=1 -D .

# ---------------------------------------------------------------------------
# Version 6: continuous editing -- open the entry in Isabelle/jEdit instead
# of batch building.
# ---------------------------------------------------------------------------
# "$ISABELLE" jedit -d . -l HOL FatioFaithful_tests.thy
