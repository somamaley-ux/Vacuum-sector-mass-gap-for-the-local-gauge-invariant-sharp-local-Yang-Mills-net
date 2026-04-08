# Hostile-read protocol (Phase 7)

Purpose: run the three hostile reads required by the clay-level closure plan before any journal submission.

## Frozen input packet
Every reviewer receives the same frozen package:
- the compiled manuscript PDF from `main.tex`,
- the source hash from `06_source_manifest_sha256.txt`,
- this protocol,
- the reviewer-specific packet below.

## Reviewer classes
1. **PDE analyst**
2. **Foundations / scope critic**
3. **Generalist proof auditor**

## Non-negotiable reporting rule
Every surviving objection must be written in one of the following forms:
- “The statement of Theorem/Proposition/Lemma X appears false or overbroad because ...”
- “The proof of Theorem/Proposition/Lemma X does not establish Y because ...”
- “Definition X / bridge lemma Y / appendix input Z is insufficient because ...”
- “Primitive assumption A is being used in a stronger form than stated because ...”

No objection may survive in the vague form:
- “this feels circular,”
- “12F is obviously the whole engine,”
- “this might be outside the framework,”
- “the paper seems to rely on philosophy,”
- or “the endpoint probably still escapes.”

## Required output fields for every objection
- ID
- Reviewer class
- Exact theorem / definition / appendix label(s)
- Quoted triggering passage
- Category: statement / proof / dependency / exposition
- Severity: fatal / major / medium / minor
- Suggested repair, if any
- Whether the objection survives after local-label review
- If the objection concerns the 12F / 12G / P4 seam: whether it attacks 12F as a premise, 12G/P4 as the first exclusion node, or a downstream transport step

## Author-side triage rule
For each objection, record one of:
- **Accepted theorem issue** - manuscript change required
- **Accepted exposition issue** - wording / navigation change required
- **Rejected** - theorem-local answer already exists in the current PDF
- **Primitive disagreement** - the reviewer is denying a named primitive assumption rather than pointing to an internal gap

## Exit condition
Do not submit until:
- each reviewer has filed a written packet,
- every surviving issue is indexed to a named label or primitive assumption,
- the manuscript hash and QA report are updated after any revision.
