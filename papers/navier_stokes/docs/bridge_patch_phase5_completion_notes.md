# Bridge-patch Phase 5 completion notes

Phase 5 implements the endgame-visibility / Appendix-F audit step from `Clay_hardening_plan_12F_bridge_patch.pdf`.

Completed in this phase:

- added a page-1 **Bridge-patch live dependency chain** paragraph making the two carried channels explicit:
  - `12F -> 12G/P4 -> 13K -> 20.5B -> 20B`, and
  - `12F -> 12G/P4 -> ST2--ST3 -> 20C.1 -> 20C`;
- updated the front-matter theorem map with a dedicated row sending the reader to the audited bridge-to-endgame chain in one place;
- added a compact glossary entry naming the same bridge-dependency chain explicitly;
- strengthened the compressed proof spine intro so it now points to the unique carried channels before the reader reaches the enumerated route;
- added a dedicated denial-map row for the objection that `12F` is still acting as the standalone no-second-gate engine;
- expanded Appendix `F` with a one-place, node-by-node dependency table for `12F / 12G / 13K / 20.5B / 20B / ST3 / 20C`, together with an explicit one-route summary sentence.

Exit condition addressed:

A hostile reader can now verify the clarified dependency order without reconstructing it from dispersed citations, and the manuscript states plainly that this audited chain is the only route by which the official theorem is obtained.
