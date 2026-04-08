# Navier--Stokes Lean Status

## Current state

The Navier--Stokes project in this repository is in a strong manuscript-facing
formalized state.

What is finished:

- the primitive route is encoded in Lean
- the manuscript-facing claim structure is encoded
- actual extracted subsection titles are mapped into the Lean surface
- actual extracted theorem titles are mapped into the Lean surface
- the dependency spine is encoded
- the vortex-stretching seam is isolated explicitly
- the final surface is axiom-free at the manuscript-facing level

What is not finished:

- a full end-to-end classical PDE proof of the periodic 3D Navier--Stokes
  theorem in Lean

## Final manuscript-facing layers

The current final surface is centered on:

- `MaleyLean/NavierStokesVerbatimSubsectionRegister.lean`
- `MaleyLean/NavierStokesVerbatimTheoremRegister.lean`
- `MaleyLean/NavierStokesVerbatimDependencySpineSimple.lean`
- `MaleyLean/NavierStokesVortexStretchingNonLoadBearing.lean`
- `MaleyLean/NavierStokesNoHiddenScopeChange.lean`
- `MaleyLean/NavierStokesPaperSurfaceSummaryClean.lean`

## What the formalization says

The current Lean development supports the following reading.

- The structural route is formalized and certified.
- The remaining live seam is isolated at vortex stretching.
- The endpoint theorem titles are downstream of that seam.
- Vortex stretching is not treated as "the one missing PDE estimate."
- Once typed as bookkeeping-visible only, vortex stretching cannot itself act
  as a same-scope continuation gate.
- Any attempt to make it continuation-decisive would require either a hidden
  second gate or a loss of same-scope status.

## Why this matters

This makes the project much more precise than a vague "gap remains" story.
The current Lean surface says exactly where the unresolved pressure lies and
why the project does not regard that seam as a routine PDE patch.

It also makes the methodological posture explicit: a successful resolution is
not required to be purely PDE-native if the official theorem is closed honestly
by a genuinely new structural route.

## Main verification artifacts

The most relevant axiom checks are:

- `NavierStokesVerbatimSubsectionRegisterAxiomCheck.lean`
- `NavierStokesVerbatimTheoremRegisterAxiomCheck.lean`
- `NavierStokesVerbatimDependencySpineSimpleAxiomCheck.lean`
- `NavierStokesVortexStretchingNonLoadBearingAxiomCheck.lean`
- `NavierStokesNoHiddenScopeChangeAxiomCheck.lean`
- `NavierStokesPaperSurfaceSummaryCleanAxiomCheck.lean`

Their matching audit files report these finalized layers as axiom-free.

## Best next directions

If this project is pushed further, the highest-value directions are:

1. strengthen the endpoint reduction on the primitive side
2. continue tightening the manuscript mirror claim-by-claim
3. connect the Navier--Stokes route more explicitly to the broader corpus
4. archive or remove remaining stale temp artifacts that are unrelated to the
   final surface
