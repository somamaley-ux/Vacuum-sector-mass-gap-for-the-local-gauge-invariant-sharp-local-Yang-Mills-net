# Public errata policy

## Purpose
This policy governs post-submission and post-publication corrections for the standalone manuscript.

## Rules
1. **No silent theorem changes.** Any change to a theorem statement, proof, appendix dependency, or front-matter claim map requires a version bump and a public note.
2. **Expository vs substantive split.**
   - Expository edits: wording, navigation, typo fixes, formatting, label cleanup.
   - Substantive edits: theorem statements, proofs, dependency architecture, appendix load-bearing status, bibliography items that affect proof accessibility.
3. **Versioning.**
   - Every public revision gets a new version identifier and date.
   - Every public revision is paired with a refreshed source hash manifest.
4. **Diff discipline.**
   - Substantive revisions must be accompanied by a theorem-local change log identifying every affected label.
5. **Archive discipline.**
   - Keep all prior public versions available.
   - Never overwrite the accepted or published source bundle without preserving the prior version.
6. **Public acknowledgment.**
   - If a reader identifies a real issue, acknowledge it publicly and state whether the repair is expository or substantive.
7. **No side-note dependence.**
   - An errata note may explain a change, but the repaired proof must be incorporated into the manuscript itself if it is truly load-bearing.

## Public channels
- arXiv / public preprint page (if used)
- journal correction channel (if applicable)
- public source bundle release page
- theorem-local response document

## Non-goal
The errata policy is not a substitute for the proof. It exists to preserve trust and auditability once the paper enters public scrutiny.
