# Clay-oriented Phase II completion notes

This repository snapshot implements **Phase II** of `Clay_oriented_hardening_plan_NS.pdf` on top of the Phase I baseline.

## What Phase II adds

1. **Manuscript-local standing/intelligibility packet**
   - Added the fixed-periodic packet `ST1--ST3` in Part II:
     - `ST1`: standing-positive continuation-relevant determination at fixed periodic scope
     - `ST2`: intelligibility failure is standing loss
     - `ST3`: standing--admissibility equivalence / no neutral same-scope status
   - Added the realized-lineage packet `ST4--ST5` in Part III:
     - `ST4`: standing conservation / no standing-neutral drift on realized lineages
     - `ST5`: irreversibility of representational commitment on realized lineages

2. **Companion-paper burden removed from the live manuscript**
   - The standing/intelligibility papers discussed during hardening are now provenance only.
   - Appendix F now contains an explicit Phase II mapping from the former external burdens to the exact in-manuscript theorem labels carrying them locally.

3. **Front-matter and audit updates**
   - Updated the primitive dependency declaration to state that ST1--ST5 are now manuscript-local.
   - Added theorem-map / denial-map / glossary entries showing where the packet now lives inside the PDF.
   - Kept the endgame and endpoint compression honest: Phase II internalizes the packet, but does **not yet** rewrite the final two-branch closure. That remains Phase III / IV work under the hardening plan.

## Files changed in Phase II
- `frontmatter/01_frontmatter.tex`
- `parts/part2_primitive_certification.tex`
- `parts/part3_faithful_classical_realization.tex`
- `appendices/appF_audit_aids.tex`
- `README.md`
- `docs/clay_phase2_completion_notes.md`

## Exit-gate status
Phase II's exit gate is now met in the manuscript-local sense intended by the hardening plan: the four standing/intelligibility companion papers can be removed without depriving the submission PDF of the theorem-local packet they were supplying during analysis.

## What remains for later phases
- Phase III: explicit same-scope continuation-failure dichotomy
- Phase IV: endgame rewrite around the standing-positive witness branch and the standing-failure branch
- Phase V: bridge/handoff theorem-local repairs where needed
