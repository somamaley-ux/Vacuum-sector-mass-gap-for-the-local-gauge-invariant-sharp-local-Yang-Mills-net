# Yang--Mills Hostile Referee Audit

Last updated: 2026-04-19

## Purpose

This note records the main hostile-referee objections the current Yang--Mills
extension package should be expected to face, together with the current best
repo-grounded answers.

The goal is not to overclaim. The goal is to make the remaining attack surface
explicit.

## Objection 1

"The extension paper still has several Section 8 routes, so the endpoint
theorem is not genuinely fixed."

Current answer:

- The canonical Section 8 theorem surface is fixed in code.
- The nearby structured-bridge, boundary-bridge, and patched-assumption-bundle
  routes are now explicitly collapsed back onto that canonical theorem surface.

Most relevant surfaces:

- `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean`
- `YMSection8_CanonicalPreferredEndpointTheorem`
- `YMSection8_CanonicalPreferredClayEndpoint`
- `YMSection8_PreferredClayEndpointFromStructuredBridgeTarget_eq_canonical`
- `YMSection8_PreferredClayEndpointFromClosedManuscriptBoundaryBridgeViaRoute1EndpointSecondSeam_eq_canonical`
- `YMSection8_PreferredClayEndpointFromClosedManuscriptBoundaryBridgeViaRoute1EndpointPaperSecondSeam_eq_canonical`
- `YMSection8_PreferredClayEndpointFromPatchedAssumptionBundleTargetOfBoundaryBridge_eq_canonical`

## Objection 2

"Section 4 still sounds like a preferred packaging choice rather than a fixed
theorem-scope class."

Current answer:

- The theorem-scope package and bridge are canonically named in code.
- The post-freeze manuscript-faithfulness pass now describes them explicitly as
  the fixed Section 4 route carried by the current extension stack.

Most relevant surfaces:

- `MaleyLean/Papers/YangMills/Extension/EndpointTheoremScopeObjects.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointTaggedTheoremScopeRealization.lean`
- `YMSection4CanonicalTheoremScopePackage`
- `YMSection4CanonicalTheoremScopeBridge`
- `YMSection4CanonicalTheoremScopePackageBridge`

## Objection 3

"Section 7 is still only loosely connected to the chosen Section 4 bridge."

Current answer:

- The Section 7 recovery package is attached directly to the chosen theorem-scope
  bridge.
- The preferred Section 7 corollaries are now also described as the fixed
  post-freeze recovery route, not as one optional downstream presentation.

Most relevant surfaces:

- `MaleyLean/Papers/YangMills/Extension/EndpointGlobalFormRecoveryFormalization.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointTaggedManuscriptCorollaries.lean`
- `YMCompanionIIIGlobalFormRecoveryPackage`
- `YMCompanionIIIGlobalFormRecoveryPackageFromDistinction`
- `YMSection7_PreferredGlobalFormRecovery`
- `YMSection7_PreferredGlobalFormRecoveryOfPackage`

## Objection 4

"The project is still only a theorem register plus status prose."

Current answer:

- The extension package is not merely a register layer.
- The four highest-risk analytic seams are isolated as local Lean-facing seam
  files with reduced payloads, route recoveries, and reconstruction equalities.

Most relevant surfaces:

- `MaleyLean/Papers/YangMills/Extension/VacuumGapConcreteCriticalSeam.lean`
- `MaleyLean/Papers/YangMills/Extension/VacuumGapConcreteOSTimeUpgradeProjection.lean`
- `MaleyLean/Papers/YangMills/Extension/VacuumGapConcreteContinuumTransportProjection.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean`

## Objection 5

"The repo still blurs what is mechanized in Lean and what remains proof-home
dependent."

Current answer:

- The current package is strong at the manuscript-facing and decisive-seam
  levels.
- It still does not claim a full first-principles Lean derivation of every
  cited analytic proof home.
- That distinction is now stated repeatedly in the dossier and submission notes.

Most relevant surfaces:

- `reports/status/yang_mills_solution_dossier.md`
- `reports/submission/yang_mills_completion_memo_2026-04-19.md`
- `reports/submission/yang_mills_referee_verification_note_2026-04-15.md`

## Objection 6

"The post-freeze edits look like reopening the extension package rather than
stabilizing it."

Current answer:

- The theorem content remains frozen at the `ym-paper-v1.2.1` boundary.
- The current edits are explicitly documented as manuscript-faithfulness polish
  on top of that frozen theorem content.

Most relevant surfaces:

- `reports/status/yang_mills_post_freeze_roadmap.md`
- `reports/status/yang_mills_extension_status.md`

## Current honest residual risk

The remaining risk is now concentrated in presentation discipline, not hidden
critical-seam mathematics.

The two live presentation risks are:

- whether the Section 4 theorem-scope object is described in the most
  manuscript-faithful possible wording
- whether every remaining Section 8 support route is read immediately as
  subordinate support infrastructure rather than theorem-level multiplicity

That is a much narrower attack surface than the repo had before the extension
hardening pass.
