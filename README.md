# MaleyLean

## Navier--Stokes formalization status

This repository now contains a manuscript-facing Lean scaffold for the
Navier--Stokes project behind:

`Carrier Universality and Global Smoothness for the Periodic 3D Navier--Stokes Equations`

The current formalization is intentionally primitives-first. It does not claim
to be a full Lean proof of the classical periodic 3D Navier--Stokes global
regularity theorem from standard analysis alone. Instead, it formalizes the
structural route, the manuscript-facing claim map, and the exact point where
the remaining analytic burden sits.

### What is formalized

- A primitive core for carrier, standing, admissibility, continuation, horizon
  witness, restart transport, maximal-lineage closure, and no-second-gate
  reasoning.
- A primitive no-blowup boundary stated honestly as a structural result, with
  restart transport kept explicit rather than hidden.
- A primitive-to-PDE obligation register and concrete obligation inventory.
- A verbatim subsection register keyed to actual extracted manuscript titles.
- A verbatim theorem register keyed to actual extracted theorem, lemma,
  proposition, and corollary titles.
- A verbatim dependency spine showing which theorem titles are structurally
  closed, which title marks the named failure boundary, and which endpoint
  titles remain downstream of that boundary.
- A vortex-stretching non-load-bearing layer stating that once the observable
  is typed as bookkeeping-visible only, it cannot also function as a
  same-scope continuation gate.

### What is closed

The Lean surface certifies the structural part of the manuscript route as
axiom-free. In particular, the current finalized manuscript-facing layers are:

- `MaleyLean.NavierStokesVerbatimSubsectionRegister`
- `MaleyLean.NavierStokesVerbatimTheoremRegister`
- `MaleyLean.NavierStokesVerbatimDependencySpineSimple`
- `MaleyLean.NavierStokesVortexStretchingNonLoadBearing`
- `MaleyLean.NavierStokesPaperSurfaceSummaryClean`

The top-level summary theorem in
`MaleyLean.NavierStokesPaperSurfaceSummaryClean` packages the current state
into one axiom-free manuscript-facing statement.

### What is not claimed

This repository does not currently claim:

- a full end-to-end Lean proof of periodic 3D Navier--Stokes global smoothness
  in the usual PDE sense
- closure of the missing analytic bridge at the vortex-stretching step
- replacement of the named analytic burden with a hidden structural shortcut

### Methodological posture

This project is explicit about method: a successful resolution does not need to
be a purely PDE-native proof in order to matter. The Clay target is the
official periodic regularity theorem itself, not allegiance to one pre-fixed
proof style.

Accordingly, this repository does not assume that the remaining work must be
completed by extracting one more classical vortex-stretching estimate. It
proceeds on the view that genuinely new methods may be required, and that a
structural or primitive route is legitimate so long as it closes the official
theorem honestly and without hidden scope changes.

### Named analytic boundary

The remaining analytic burden is isolated explicitly rather than blurred across
the development.

- Named failure boundary:
  `Pointwise vortex-stretching gate collapse`
- Downstream endpoint titles:
  `Official periodic theorem on T^3 (Fefferman (B); official classical restatement of Corollary 21A)`
  and
  `No finite-time blow-up on the official periodic carrier`

In the current Lean surface, those endpoint titles are marked as downstream of
the named vortex-stretching failure line.

The current formalization also sharpens the interpretation of that line: it is
not treated as "one more PDE estimate waiting to be found." Instead, the Lean
surface now records that if vortex-stretching data is only bookkeeping-visible
at fixed scope, then it is non-load-bearing and cannot itself decide
continuation. On that reading, any attempt to make it continuation-decisive
would amount to introducing a hidden second gate.

### How to read the current surface

If you want the shortest path through the finalized Navier--Stokes layer, read
these in order:

1. `MaleyLean/NavierStokesPrimitiveNoBlowup.lean`
2. `MaleyLean/NavierStokesPDEObligationInventory.lean`
3. `MaleyLean/NavierStokesVerbatimSubsectionRegister.lean`
4. `MaleyLean/NavierStokesVerbatimTheoremRegister.lean`
5. `MaleyLean/NavierStokesVerbatimDependencySpineSimple.lean`
6. `MaleyLean/NavierStokesVortexStretchingNonLoadBearing.lean`
7. `MaleyLean/NavierStokesPaperSurfaceSummaryClean.lean`

### Verification

The final manuscript-facing Navier--Stokes surface has dedicated axiom checks,
including:

- `NavierStokesVerbatimSubsectionRegisterAxiomCheck.lean`
- `NavierStokesVerbatimTheoremRegisterAxiomCheck.lean`
- `NavierStokesVerbatimDependencySpineSimpleAxiomCheck.lean`
- `NavierStokesVortexStretchingNonLoadBearingAxiomCheck.lean`
- `NavierStokesPaperSurfaceSummaryCleanAxiomCheck.lean`

Their audit files report the finalized surface as axiom-free.
