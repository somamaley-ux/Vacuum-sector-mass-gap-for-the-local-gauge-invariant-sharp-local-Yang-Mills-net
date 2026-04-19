# Yang--Mills Extension Referee Note

Last updated: 2026-04-19

## Purpose

This note records the current hostile-referee answer to the question:

"Why is the remaining multiplicity in the extension stack not a live
mathematical ambiguity?"

## Short answer

Because the main endpoint theorem surface is now fixed.

The Section 8 compatibility layer now has:

- one canonical manuscript-facing Section 8 theorem surface
- one canonical combined Section 7 plus Section 8 corollary
- multiple explicit equalities showing that the nearby structured and
  boundary-bridge routes collapse back to that canonical theorem

So the remaining multiplicity is not "several possible endpoint theorems."
It is "several access routes and exactness wrappers around one endpoint theorem."

## What Is Canonical Now

The preferred Section 8 theorem surface is the patched Route 1 second-seam
theorem named in:

- `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean`

The canonical theorem-facing names are:

- `YMSection8_CanonicalPreferredEndpointTheorem`
- `YMSection8_CanonicalPreferredClayEndpoint`
- `YMSection7And8_CanonicalPreferredEndpointCorollary`

These are now the right theorem surfaces to cite when describing the extension
paper's final Section 8 endpoint claim.

## Why The Other Routes Still Exist

The other routes remain because they record provenance and paper-faithful
transport, not because the endpoint theorem is unsettled.

They serve three useful roles:

- they show how the old boundary bridge feeds the canonical theorem
- they show how the structured bridge and patched assumption bundle are exact
  reformulations of the same endpoint content
- they preserve source-route traceability back to proof-home and Route 1
  second-seam inputs

This is valuable for auditability. It is no longer evidence of theorem-level
indecision.

## What Still Looks Residual

Two residuals remain, but they are now narrower than before:

- the theorem-scope class still wants its most paper-faithful final concrete
  presentation
- some Section 8 access routes still read a little too much like standalone
  theorem endpoints instead of obviously subordinate support lemmas

So the remaining work is mostly presentation discipline and final theorem-scope
closure, not missing endpoint mathematics.

## Current Claim Discipline

The honest claim is:

- the four critical seams are mechanized
- the Section 8 endpoint theorem surface is canonically fixed
- the remaining alternate Section 8 formulations are now best read as support
  infrastructure around that fixed theorem
- the extension stack is very close to a finished referee-facing package, but
  not yet at the point where every residual presentation choice has been fully
  flattened
