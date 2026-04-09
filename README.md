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

- `MaleyLean.Papers.NavierStokes.Verbatim.SubsectionRegister`
- `MaleyLean.Papers.NavierStokes.Verbatim.TheoremRegister`
- `MaleyLean.Papers.NavierStokes.Verbatim.DependencySpineSimple`
- `MaleyLean.Papers.NavierStokes.Surface.VortexStretchingNonLoadBearing`
- `MaleyLean.Papers.NavierStokes.Surface.SummaryClean`

The top-level summary theorem in
`MaleyLean.Papers.NavierStokes.Surface.SummaryClean` packages the current state
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

1. `MaleyLean/Papers/NavierStokes/Primitive/NoBlowup.lean`
2. `MaleyLean/Papers/NavierStokes/Obligations/Inventory.lean`
3. `MaleyLean/Papers/NavierStokes/Verbatim/SubsectionRegister.lean`
4. `MaleyLean/Papers/NavierStokes/Verbatim/TheoremRegister.lean`
5. `MaleyLean/Papers/NavierStokes/Verbatim/DependencySpineSimple.lean`
6. `MaleyLean/Papers/NavierStokes/Surface/VortexStretchingNonLoadBearing.lean`
7. `MaleyLean/Papers/NavierStokes/Surface/SummaryClean.lean`

### Verification

The final manuscript-facing Navier--Stokes surface has dedicated axiom checks
under `Checks/Axiom/`, including:

- `Checks/Axiom/NavierStokesVerbatimSubsectionRegisterAxiomCheck.lean`
- `Checks/Axiom/NavierStokesVerbatimTheoremRegisterAxiomCheck.lean`
- `Checks/Axiom/NavierStokesVerbatimDependencySpineSimpleAxiomCheck.lean`
- `Checks/Axiom/NavierStokesVortexStretchingNonLoadBearingAxiomCheck.lean`
- `Checks/Axiom/NavierStokesPaperSurfaceSummaryCleanAxiomCheck.lean`

Their audit files now live under `reports/audits/` and report the finalized
surface as axiom-free.

## Yang--Mills formalization status

This repository now also contains a manuscript-facing Lean scaffold for the
Yang--Mills project built from the hardened core-plus-companions archive.

The current Yang--Mills formalization is structural and manuscript-facing. It
does not claim a full Lean formalization of the underlying QFT/PDE proofs.
Instead, it encodes:

- the live proof surface and companion ownership map
- the verbatim theorem register
- the dependency spine
- the obligation, paper, and claim ledgers
- the proof-kernel extraction
- the ten-packet kernel reduction
- the decisive seam nodes
- the source-label crosswalk back to the canonical manuscript
- a load-bearing proof spine with dedicated Part C, Part D, and endpoint cores
- a named-output witness layer collecting constructive, gap, and endpoint exports
- an additive Part C witness crosswalk for finite-cap and sharp-local exports
- an additive endpoint witness crosswalk for reconstruction and exact-endpoint exports
- a witness-to-packet/source crosswalk for those named abstract exports
- an additive Part D witness crosswalk for OS transport and transport-origin exports
- a structured witness bundle object collecting the three theorem-heart exports
- a unified witness-heart summary tying the constructive, vacuum-gap, and endpoint witness bundles together
- a surface-level witness-bundle summary exporting that bundle at manuscript-facing level
- a surface-level semantic-assembly summary exporting the unified three-heart semantic object

### Current Yang--Mills surface

The main Yang--Mills entry points are:

- `MaleyLean.Papers.YangMills.Verbatim.TheoremRegister`
- `MaleyLean.Papers.YangMills.Verbatim.DependencySpineSimple`
- `MaleyLean.Papers.YangMills.Obligations.ClaimLedger`
- `MaleyLean.Papers.YangMills.Kernel.Register`
- `MaleyLean.Papers.YangMills.Kernel.PacketRegister`
- `MaleyLean.Papers.YangMills.Kernel.ConstructiveCore`
- `MaleyLean.Papers.YangMills.Kernel.VacuumGapCore`
- `MaleyLean.Papers.YangMills.Kernel.EndpointCore`
- `MaleyLean.Papers.YangMills.Kernel.NamedOutputsAssembly`
- `MaleyLean.Papers.YangMills.Kernel.SeamRegister`
- `MaleyLean.Papers.YangMills.SourceCrosswalk.Register`
- `MaleyLean.Papers.YangMills.SourceCrosswalk.ConstructiveWitnessRegister`
- `MaleyLean.Papers.YangMills.SourceCrosswalk.EndpointWitnessRegister`
- `MaleyLean.Papers.YangMills.SourceCrosswalk.WitnessRegister`
- `MaleyLean.Papers.YangMills.SourceCrosswalk.VacuumGapWitnessRegister`
- `MaleyLean.Papers.YangMills.Kernel.WitnessBundle`
- `MaleyLean.Papers.YangMills.Kernel.SemanticAssembly`
- `MaleyLean.Papers.YangMills.Surface.SemanticAssemblySummary`
- `MaleyLean.Papers.YangMills.Surface.WitnessBundleSummary`
- `MaleyLean.Papers.YangMills.Surface.WitnessHeartSummary`
- `MaleyLean.Papers.YangMills.Surface.Summary`

The top-level summary theorem in
`MaleyLean.Papers.YangMills.Surface.Summary` packages the current
manuscript-facing Yang--Mills scaffold into one axiom-free statement.

### Yang--Mills verification

The current Yang--Mills scaffold has dedicated axiom checks under
`Checks/Axiom/`, including:

- `Checks/Axiom/YangMillsVerbatimTheoremRegisterAxiomCheck.lean`
- `Checks/Axiom/YangMillsClaimLedgerAxiomCheck.lean`
- `Checks/Axiom/YangMillsKernelRegisterAxiomCheck.lean`
- `Checks/Axiom/YangMillsPacketRegisterAxiomCheck.lean`
- `Checks/Axiom/YangMillsSeamRegisterAxiomCheck.lean`
- `Checks/Axiom/YangMillsConstructiveCoreAxiomCheck.lean`
- `Checks/Axiom/YangMillsVacuumGapCoreAxiomCheck.lean`
- `Checks/Axiom/YangMillsEndpointCoreAxiomCheck.lean`
- `Checks/Axiom/YangMillsNamedOutputsAssemblyAxiomCheck.lean`
- `Checks/Axiom/YangMillsSourceCrosswalkAxiomCheck.lean`
- `Checks/Axiom/YangMillsConstructiveWitnessCrosswalkAxiomCheck.lean`
- `Checks/Axiom/YangMillsEndpointWitnessCrosswalkAxiomCheck.lean`
- `Checks/Axiom/YangMillsWitnessCrosswalkAxiomCheck.lean`
- `Checks/Axiom/YangMillsVacuumGapWitnessCrosswalkAxiomCheck.lean`
- `Checks/Axiom/YangMillsWitnessBundleAxiomCheck.lean`
- `Checks/Axiom/YangMillsSemanticAssemblyAxiomCheck.lean`
- `Checks/Axiom/YangMillsSemanticAssemblySummaryAxiomCheck.lean`
- `Checks/Axiom/YangMillsWitnessBundleSummaryAxiomCheck.lean`
- `Checks/Axiom/YangMillsWitnessHeartSummaryAxiomCheck.lean`
- `Checks/Axiom/YangMillsPaperSurfaceSummaryAxiomCheck.lean`

See `reports/status/yang_mills_status.md` for the current Yang--Mills project
status note.
