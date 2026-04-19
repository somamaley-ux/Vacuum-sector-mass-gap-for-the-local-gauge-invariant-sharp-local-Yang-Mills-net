# Yang--Mills Extension Finish Checklist

Last updated: 2026-04-19

## What Is Already Strong

The extension paper is not stuck at the level of vague intentions.

The following are already materially in place:

- the four critical seams are isolated and mechanized
- the Section 4 theorem-scope object layer exists
- the Section 7 global-form recovery surface exists
- the Section 8 endpoint/admissibility hierarchy exists
- the main QE3 and endpoint source routes are reconstruction-explicit
- the remaining endpoint-side gap is documented in the code as packaging rather
  than new mathematical content

So this checklist is not a "build the extension paper from scratch" list. It is
the narrow closure list between "very strong hardened extension stack" and
"finished extension paper."

## Finish Target 1

Concrete paper-faithful theorem-scope class

Current state:

- `MaleyLean/Papers/YangMills/Extension/EndpointAdmissibilityFormalization.lean`
  now presents the theorem-scope bridge as infrastructure while still leaving
  the most paper-faithful closure of the class specification as a residual.
- `MaleyLean/Papers/YangMills/Extension/EndpointConcreteTheoremScopeBridge.lean`
  now treats the constant-carrier route as baseline infrastructure rather than
  the final paper-facing classification layer.
- `MaleyLean/Papers/YangMills/Extension/EndpointTaggedTheoremScopeRealization.lean`
  now provides the canonical current paper-facing theorem-scope bridge naming.

To call this closed, we want:

- one clearly preferred theorem-scope support/label class presented as the
  paper's final concrete class, not only as an abstract carrier plus support
  and deformation interface
- one clearly preferred realization statement explaining how that class lands in
  the reconstructed-sector carrier
- the corresponding docs updated so they no longer describe this point as an
  open strengthening target

Primary target files:

- `MaleyLean/Papers/YangMills/Extension/EndpointTheoremScopeObjects.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointConcreteTheoremScopeBridge.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointFormalizationOverview.lean`

## Finish Target 2

Final Section 8 paper-shaped bridge packaging

Current state:

- `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean`
  already documents that the remaining Section 8 target is packaging rather than
  extra mathematical content.
- `MaleyLean/Papers/YangMills/Extension/EndpointCompletionBridgeFormalization.lean`
  and `EndpointClayConclusionFormalization.lean` now expose packaged
  completion-bridge and Clay-endpoint surfaces over the canonical
  theorem-scope package.
- the file already exposes several equivalent surfaces:
  the patched theorem statement, the structured bridge object, and the full
  manuscript-shaped assumption bundle.
- the code also isolates the single genuinely non-automatic extra ingredient:
  the Route 1 paper-second seam to admissibility implication.

To call this closed, we want:

- one preferred final Section 8 statement surface chosen as the paper-facing
  canonical version
- one preferred proof route to that surface chosen as the standard route
- the remaining "equivalent bridge shapes" demoted to support lemmas rather than
  still reading like live candidate endpoints
- the docs updated so they describe the remaining Section 8 work as
  compatibility-route standardization rather than as a still-missing endpoint
  package layer

Primary target files:

- `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointClayConclusionFormalization.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointFormalizationOverview.lean`

## Practical Done Condition

I would call the extension paper finished when all of the following are true:

1. the theorem-scope class is described in one preferred final concrete form
2. the Section 8 endpoint bridge is described in one preferred final
   manuscript-facing form
3. `EndpointFormalizationOverview.lean` reads as a closed dependency overview
   rather than an overview with named residual targets
4. the human-facing docs stop describing theorem-scope instantiation and Section
   8 packaging as open strengthening targets

## Best Next Work

If we want the highest-value next pass, it is:

1. choose the final preferred theorem-scope class presentation
2. choose the final preferred Section 8 bridge statement
3. collapse the remaining alternatives into lemmas/corollaries
4. update the extension overview and status notes to mark the extension paper as
   finished

For the implementation-level version of this closure plan, see
`reports/status/yang_mills_extension_implementation_agenda.md`.
