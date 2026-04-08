# Yang--Mills Lean Status

## Current state

The Yang--Mills project in this repository is now in a strong
manuscript-facing structural state.

What is finished:

- the live proof surface is encoded in Lean
- the core theorem titles are encoded
- the companion ownership map is encoded
- the live dependency spine is encoded
- the proof-kernel extraction is encoded
- the ten-packet reduction is encoded
- the decisive seam nodes are encoded
- the source-label crosswalk back to the canonical manuscript is encoded
- the top-level manuscript-facing summary is axiom-free

What is not finished:

- a full end-to-end Lean formalization of the underlying Yang--Mills QFT/PDE
  mathematics
- discharge in Lean of the analytic arguments cited by the manuscript proof
  homes
- replacement of the companion/source proofs with native Lean proofs

## Final manuscript-facing layers

The current Yang--Mills surface is centered on:

- `MaleyLean/Papers/YangMills/Verbatim/TheoremRegister.lean`
- `MaleyLean/Papers/YangMills/Verbatim/DependencySpineSimple.lean`
- `MaleyLean/Papers/YangMills/Obligations/Inventory.lean`
- `MaleyLean/Papers/YangMills/Obligations/PaperLedger.lean`
- `MaleyLean/Papers/YangMills/Obligations/ClaimLedger.lean`
- `MaleyLean/Papers/YangMills/Kernel/Register.lean`
- `MaleyLean/Papers/YangMills/Kernel/PacketRegister.lean`
- `MaleyLean/Papers/YangMills/Kernel/SeamRegister.lean`
- `MaleyLean/Papers/YangMills/SourceCrosswalk/Register.lean`
- `MaleyLean/Papers/YangMills/Surface/Summary.lean`

## What the formalization says

The current Lean development supports the following reading.

- The hardened Yang--Mills archive has a four-root live proof surface.
- `proofkernel.tex` is an expert-audit extraction, not a second source of new
  mathematics.
- The public theorem burden is organized by ten packets plus one auxiliary
  weak-window certificate.
- The decisive expert-attack seams are explicit rather than hidden in prose.
- The cleaned public theorem nodes are crosswalked back to canonical source
  labels such as `F.331`, `5.74`, `F.216`, `M.3`, and `O.5`.

## Why this matters

This makes the Yang--Mills manuscript much easier to interrogate honestly.
The Lean surface now says:

- what counts as live proof burden,
- what is only audit extraction,
- what is only closure packaging,
- what remains reserve support material,
- and how the public theorem surface maps back to the source manuscript.

That does not prove the Yang--Mills mathematics in Lean, but it does remove a
large amount of ambiguity about manuscript structure, dependency order, and
seam locality.

## Main verification artifacts

The most relevant axiom checks are:

- `YangMillsVerbatimTheoremRegisterAxiomCheck.lean`
- `YangMillsClaimLedgerAxiomCheck.lean`
- `YangMillsKernelRegisterAxiomCheck.lean`
- `YangMillsPacketRegisterAxiomCheck.lean`
- `YangMillsSeamRegisterAxiomCheck.lean`
- `YangMillsSourceCrosswalkAxiomCheck.lean`
- `YangMillsPaperSurfaceSummaryAxiomCheck.lean`

These checks report the current manuscript-facing Yang--Mills surface as
axiom-free.

## Best next directions

If this project is pushed further, the highest-value directions are:

1. add a subsection and reading-order register mirroring the kernel attack
   guidance
2. extend the source crosswalk to more of the companion-local theorem tables
3. write theorem-by-theorem support maps or audits parallel to the existing
   Navier--Stokes reporting style
4. begin replacing selected structural packet statements with deeper native
   Lean abstractions where the mathematics is stable enough
