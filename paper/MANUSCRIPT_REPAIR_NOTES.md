# Manuscript repair notes (Phase-I proof-surface freeze)

This pass executes Phase I of the closure plan: freeze the live proof surface, canonicalize numbering/routing, and separate live proof from reserve material.

Applied repairs:
- Added a new core appendix `appendixC_phase1_freeze.tex` containing:
  - the master theorem index;
  - the canonical numbering crosswalk;
  - the companion-only live seam table.
- Rebuilt the core packet-docket appendix as the frozen live dependency docket:
  - packet descriptions now isolate proof-local hardening nodes;
  - the DAG now shows Packet 8 consuming Lane A seam results;
  - F.298 is surfaced as the sole live weak-window certificate;
  - Lane B is explicitly excluded as downstream only.
- Hardened the live-versus-reserve boundary:
  - core Appendix B now states the live proof surface explicitly;
  - each companion front matter now carries the Phase-I proof-surface freeze statement;
  - reserve routing appendices P and Q are marked as reserve-only routing aids.
- Updated repository notes (`README.md`, `BUILD_NOTES.md`) so the Overleaf project itself advertises the same live/reserve split.

Build status:
- All four live roots (`core.tex`, `companion1.tex`, `companion2.tex`, `companion3.tex`) were rebuilt successfully after these edits.
