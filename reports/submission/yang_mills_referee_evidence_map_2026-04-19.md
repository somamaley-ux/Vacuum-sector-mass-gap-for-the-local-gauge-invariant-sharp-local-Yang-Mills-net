# Yang--Mills Referee Evidence Map

Date: 2026-04-19

## Purpose

This note is a compact bridge between the hostile-referee objection list and
the detailed Lean/code surfaces.

Use it when you want the fastest answer to:

"If I am worried about objection X, what should I read first?"

## Evidence map

| Objection | Read first | Inspect first in code |
| --- | --- | --- |
| Section 8 still has multiple routes, so the endpoint theorem is not fixed. | `reports/status/yang_mills_hostile_referee_audit.md` | `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean` |
| Section 4 still looks like a preferred packaging choice rather than a fixed class. | `reports/status/yang_mills_hostile_referee_audit.md` | `MaleyLean/Papers/YangMills/Extension/EndpointTheoremScopeObjects.lean` |
| Section 7 is not clearly attached to the chosen Section 4 route. | `reports/status/yang_mills_hostile_referee_audit.md` | `MaleyLean/Papers/YangMills/Extension/EndpointGlobalFormRecoveryFormalization.lean` |
| The repo is still only a theorem register plus status prose. | `reports/submission/yang_mills_referee_checklist_2026-04-19.md` | `MaleyLean/Papers/YangMills/Extension/VacuumGapConcreteCriticalSeam.lean` |
| The repo blurs what is mechanized in Lean and what remains proof-home dependent. | `reports/submission/yang_mills_referee_verification_note_2026-04-15.md` | `reports/status/yang_mills_solution_dossier.md` |
| The post-freeze edits reopen the package rather than stabilizing it. | `reports/status/yang_mills_post_freeze_roadmap.md` | `reports/status/yang_mills_extension_status.md` |

## Recommended escalation path

If the first file you inspect does not settle the objection, escalate in this
order:

1. `reports/status/yang_mills_hostile_referee_audit.md`
2. `reports/submission/yang_mills_referee_checklist_2026-04-19.md`
3. `reports/submission/yang_mills_completion_memo_2026-04-19.md`
4. the cited Lean extension file itself

## Fastest deep-check route

If you want the shortest route through the most sensitive extension claims, use:

1. `reports/status/yang_mills_hostile_referee_audit.md`
2. `reports/submission/yang_mills_referee_checklist_2026-04-19.md`
3. `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean`
4. `MaleyLean/Papers/YangMills/Extension/EndpointTheoremScopeObjects.lean`
5. `MaleyLean/Papers/YangMills/Extension/EndpointTaggedTheoremScopeRealization.lean`
6. `MaleyLean/Papers/YangMills/Extension/EndpointGlobalFormRecoveryFormalization.lean`
7. `MaleyLean/Papers/YangMills/Extension/EndpointTaggedManuscriptCorollaries.lean`
