# Yang--Mills Extension Implementation Agenda

Last updated: 2026-04-19

## Purpose

This note turns the extension finish checklist into a concrete implementation
agenda for the deeper closure pass.

The goal is not merely to improve wording. The goal is to remove the last two
documented sources of under-specification before calling the extension paper
finished at a serious solution-package standard.

## Workstream A

Finalize the theorem-scope class

Problem:

- `EndpointAdmissibilityFormalization.lean` still describes the bridge as not
  yet instantiating the manuscript's concrete extended-support class.
- `EndpointConcreteTheoremScopeBridge.lean` still describes the object-to-sector
  classification as isolated for later strengthening.

Implementation objective:

- choose one final preferred theorem-scope class presentation and make it the
  explicit paper-facing class rather than only one admissible abstract carrier
- choose one final preferred realization statement from that class into the
  reconstructed-sector carrier

Primary files:

- `MaleyLean/Papers/YangMills/Extension/EndpointTheoremScopeObjects.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointConcreteTheoremScopeBridge.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointTaggedTheoremScopeRealization.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointFormalizationOverview.lean`

Concrete deliverables:

1. introduce a clearly named preferred/final theorem-scope class object
2. introduce a clearly named preferred/final theorem-scope bridge theorem
3. demote the older generic bridge wording so it reads as infrastructure, not
   as the live paper-facing target
4. update overview/docs so they no longer call theorem-scope instantiation a
   remaining strengthening target

Progress:

- the preferred theorem-scope class and paper-facing bridge naming now exist in
  code
- the older constant-carrier bridge has been reframed as infrastructure
- the canonical theorem-scope package now reaches the Section 7 recovery,
  Section 8 completion bridge, Clay-endpoint package, and packaged manuscript
  corollary surfaces
- the compatibility layer now names a canonical Section 8 theorem surface and a
  canonical combined Section 7 plus Section 8 corollary
- the remaining Workstream A burden is now the final paper-faithful closure of
  that class specification rather than the absence of a canonical route

Done condition:

- the extension stack has one canonical paper-facing theorem-scope class
- the bridge docs no longer describe this layer as still abstract in the
  manuscript-facing sense

## Workstream B

Canonicalize the Section 8 bridge

Problem:

- `EndpointConcretePreferredRouteCompatibility.lean` contains the right
  mathematics, but still exposes several equivalent bridge surfaces as if the
  final paper-facing endpoint could be any of them
- `EndpointFormalizationOverview.lean` still narrates Section 8 as an active
  hierarchy of residual targets instead of as one closed preferred theorem

Implementation objective:

- choose one final manuscript-facing Section 8 statement
- choose one final proof route to it
- treat the other equivalent formulations as support lemmas, compatibility
  objects, or corollaries rather than still-live endpoint candidates

Primary files:

- `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointClayConclusionFormalization.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointTaggedManuscriptCorollaries.lean`
- `MaleyLean/Papers/YangMills/Extension/EndpointFormalizationOverview.lean`

Concrete deliverables:

1. define one clearly named canonical Section 8 theorem surface
2. define one clearly named canonical combined Section 7 plus Section 8 corollary
3. mark the patched theorem / structured bridge / manuscript bundle equivalence
   as supporting exactness rather than as competing endpoint forms
4. rewrite the overview/docs so Section 8 no longer reads as "still packaging"

Done condition:

- one paper-facing Section 8 theorem is visibly canonical
- one combined Section 7 plus Section 8 corollary is visibly canonical
- the residual Section 8 language in the overview/status notes is reduced to
  compatibility-route standardization rather than endpoint-surface selection

## Workstream C

Referee-hardening pass after closure

Problem:

- even after A and B, a hostile reader could still ask whether the final story
  is spread across too many near-equivalent surfaces

Implementation objective:

- re-audit the extension stack after A and B under the specific question
  "what still looks underspecified to a hostile Clay-level referee?"

Primary files:

- `MaleyLean/Papers/YangMills/Extension/README.md`
- `reports/status/yang_mills_extension_status.md`
- `reports/status/yang_mills_extension_finish_checklist.md`
- `reports/status/yang_mills_extension_implementation_agenda.md`

Concrete deliverables:

1. replace residual-target language with closure language if A and B are done
2. produce one short final completion note explaining why the extension paper is
   now finished rather than merely strong

## Recommended execution order

1. complete Workstream A
2. complete Workstream B
3. rerun the extension audit under hostile-referee assumptions
4. update docs and completion notes only after the code-side canonicalization is done

## Immediate next coding move

The best next implementation step is Workstream A.1:

- add a clearly named preferred theorem-scope class layer in
  `EndpointTheoremScopeObjects.lean`
- then thread that preferred object through
  `EndpointConcreteTheoremScopeBridge.lean`

That is the smallest code-side move that directly reduces one of the two live
residuals.
