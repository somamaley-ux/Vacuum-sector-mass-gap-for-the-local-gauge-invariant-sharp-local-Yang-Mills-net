# Clay-level Phase 5 completion notes

This repository snapshot implements **Phase 5** of `Clay_level_closure_plan_NS_updated.pdf` on top of the Phase 0 + Phase 1 + Phase 2 + Phase 3 + Phase 4 baseline.

## What Phase 5 adds

1. **Exact ATS role localization for the actual periodic Navier--Stokes observables used on the live route**
   - Added a new definition `13.23A.1` for **quotient-visible witness bookkeeping** so metric quantities can be described precisely without being allowed to become hidden same-scope gates.
   - Added Table `13.B` and Proposition `13.23A.2` localizing the actual periodic NS objects used in the proof: anchors, lawful skins, tensor compatibilities, the horizon discriminator, and the singular-candidate extractor.

2. **Metric divergence is now theorem-locally non-authoritative unless subordinated to an already fixed witness**
   - Added Proposition `13.23A.3` proving that critical norms, BKM-type quantities, and other metric divergences are licensed interior bookkeeping and carry no independent same-scope standing authority.
   - The same proposition also records the only licit live-route use of such quantities: quotient-visible witness bookkeeping subordinate to the pre-horizon witness, the horizon discriminator, or the later singular-candidate extractor.

3. **The paper now gives the exact trichotomy for metric singularity claims**
   - Added Proposition `13.23A.4` stating that a metric singularity claim is either (i) mere skin bookkeeping, (ii) quotient-visible witness bookkeeping, or (iii) an illicit extra gate / scope change.
   - This blocks the objection that a norm divergence can become standing-bearing simply by being expressed in metric language.

4. **Fixation-language compatibility is now internalized locally rather than left quarantined as an unresolved tension**
   - Added Proposition `13.23A.5` stating explicitly that licensed metric bookkeeping does not generate the missing analytic bridge inequality, while same-scope admissibility still governs which singularity representations are licit inside the official periodic scope.
   - Updated the front matter and Appendix F so the external fixation-persistence title remains provenance / contrast only, while the narrow compatibility statement the submission actually needs is now proved in-body.

5. **Front matter, audit appendix, and project docs now expose the new packet**
   - Updated the theorem map, glossary, compressed proof spine, denial map, and corpus-compatibility note in `frontmatter/01_frontmatter.tex`.
   - Added an updated-plan Phase-5 subsection to Appendix F and updated the source-role matrix entry for the fixation-persistence paper.
   - Updated `README.md` to reflect the new phase and created this note.

## Files changed in Phase 5
- `frontmatter/01_frontmatter.tex`
- `parts/part2_primitive_certification.tex`
- `appendices/appF_audit_aids.tex`
- `README.md`
- `docs/clay_level_phase5_completion_notes.md`

## Exit-gate status
Phase 5's exit gate is now met in the manuscript-local sense intended by the updated plan: a referee can no longer force a contradiction between `metricity is skin-level` and `the endgame excludes same-scope blow-up`, because the manuscript now states one exact theorem-local relation between those claims.

## What remains for later phases
- Phase 6: reconstruct the endgame so every endpoint branch cites the new metric / tensor / witness packet theorem-locally
- Phase 7: Clay-facing audit / attack-map / scrutiny packaging for a hostile public read
