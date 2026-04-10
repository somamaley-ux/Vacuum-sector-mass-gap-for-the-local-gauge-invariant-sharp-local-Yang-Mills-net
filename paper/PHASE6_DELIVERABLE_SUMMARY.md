# Phase VI deliverable summary

This project stages Phase VI of the clay-closure upgrade plan on top of the Phase V proof surface.

Implemented items:
- extracted a standalone proof-kernel root `proofkernel.tex` containing the exact theorem statement, the frozen live dependency DAG, the Packet 1--10 theorem route in dependency order, the finite-cap and QE3 seam details, and the endpoint packet for reconstruction and faithful-Wilson universality;
- added a one-page expert reading guide / attack-line map in `kernel/sections/00_reading_guide.tex` so that specialists can attack the kernel in the actual proof order without reserve routing notes;
- added an imported-standard-background and proof-home appendix in `kernel/appendices/appendixA_imported_background.tex` that boxes the only standard inputs and restates the live-proof boundary;
- added an exclusions appendix in `kernel/appendices/appendixB_exclusions.tex` listing what the kernel intentionally leaves out and why;
- synchronized repository notes (`README.md`, `BUILD_NOTES.md`, `PAGE_COUNTS.md`) so the Overleaf project advertises the new kernel root while preserving the Phase-I live/reserve split.

Compilation targets checked:
- `core.tex`
- `companion1.tex`
- `companion2.tex`
- `companion3.tex`
- `proofkernel.tex`
