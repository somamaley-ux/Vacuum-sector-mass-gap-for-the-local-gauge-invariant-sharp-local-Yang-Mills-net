# Build notes

This suite is configured for Overleaf / latexmk with no BibTeX step.

## Compiler
Use pdfLaTeX.

## Root files
Authoritative proof-home roots:
- `core.tex`
- `companion1.tex`
- `companion2.tex`
- `companion3.tex`

Expert-audit extraction:
- `proofkernel.tex`

Phase-IX final technical closure gate:
- `phase9_closure_gate.tex`

## Important configuration
The root `latexmkrc` disables automatic BibTeX use because the suite uses a shared manual `thebibliography` block in `shared/bibliography.tex`.

## Live proof surface / reserve split
Live proof burden:
- `core.tex`
- `companion1.tex`
- `companion2.tex`
- `companion3.tex`
- the theorem-facing appendices compiled inside those four roots

Derived expert-audit extraction:
- `proofkernel.tex` (adds no new mathematics; it is a synchronized kernel distilled from the live theorem surface and cites the same proof homes explicitly)
- kernel Appendices C--E record the Phase-VIII adversarial-verification prompts, issue protocol, kill criteria, final internal disposition log, and the Phase-IX closure-gate summary
- `phase9_closure_gate.tex` together with `closure/` records the final technical-closure pass conditions, theorem-node matrix, submission inventory, checklist, and closure memo

Reserve only:
- `support/`
- `source/appendices/appendixP_referee_audit_packet.tex`
- `source/appendices/appendixQ_executive_proof_sketch.tex`
- repository-root editorial/build notes

## Status
The suite has been checked with repeated `pdflatex` / `latexmk` builds for all four proof-home roots, for the proof-kernel root, and for the standalone `phase9_closure_gate.tex` root after the Phase-IX closure-gate additions and synchronization edits.
