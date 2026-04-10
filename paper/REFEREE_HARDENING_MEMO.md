# Referee hardening memo

This memo records the Phase-I proof-surface freeze applied to the manuscript bundle.

## What was repaired

1. **Master theorem index / canonical numbering crosswalk**
   - Added a new core appendix that freezes:
     - canonical core labels;
     - source-manuscript crosswalk labels;
     - packet assignment;
     - proof home;
     - theorem role;
     - immediate live consumers.
   - File:
     - `core/appendices/appendixC_phase1_freeze.tex`

2. **Live dependency DAG**
   - Rebuilt the packet-docket appendix so the DAG now makes three facts explicit:
     - Packet 8 consumes Lane A seam nodes;
     - Lane B is downstream only;
     - F.298 is the sole live weak-window certificate.
   - File:
     - `core/appendices/appendixA_packet_docket.tex`

3. **Live-versus-reserve boundary**
   - Added an explicit live/reserve statement to the core ledger appendix and to the front matter of all three companions.
   - Marked reserve routing appendices P and Q as reserve-only aids.
   - Files:
     - `core/appendices/appendixB_ledger_concordance.tex`
     - `companion1.tex`
     - `companion2.tex`
     - `companion3.tex`
     - `source/appendices/appendixP_referee_audit_packet.tex`
     - `source/appendices/appendixQ_executive_proof_sketch.tex`

4. **Repository-level synchronization**
   - Updated the repository notes so the Overleaf project itself advertises the same Phase-I routing split.
   - Files:
     - `README.md`
     - `BUILD_NOTES.md`
     - `MANUSCRIPT_REPAIR_NOTES.md`

## What remains intentionally unchanged

- No Phase-II theorem surgery was attempted in this pass.
- No Lane A or QE3 proof-local mathematics was changed.
- Support PDFs remain reserve materials and were not rewritten.


## Build check

The four live REVTeX roots compile after the Phase-I freeze edits:
- `core.tex`
- `companion1.tex`
- `companion2.tex`
- `companion3.tex`
