# Yang-Mills Formalization Status

Last updated: 2026-04-09

## Purpose

This note gives a human-readable snapshot of the current state of the Yang-Mills
formalization in this checkout.

It is intentionally written for readers who want to understand:

- what the repo claims to cover,
- what has actually been encoded,
- how far the current formalization appears to go,
- and what would count as meaningful next work.

## Executive Summary

Relative to the Yang-Mills paper inventory encoded in this repository, the
formalization currently appears complete.

In particular:

- the live manuscript claim families are all represented in the encoded claim ledger,
- the verbatim theorem register is present,
- the theorem-facing kernel and surface layers are present,
- the native constructive / vacuum-gap / endpoint bridge layers are present,
- the deeper cross-heart image / factorization / coherence layers are present,
- and the workflow-level verification currently passes.

The most recent verification sweep also strengthened the deepest kernel so that:

- the constructive side points explicitly to the sharp-local assembly path,
- the endpoint side points explicitly to the smear / correlate route,
- and the main cross-heart route laws are exposed as named kernel theorems rather
  than hidden definitional equalities.

## What "Complete" Means Here

The word "complete" in this note is relative to the paper-facing inventory that
already exists inside this checkout.

That means:

- every locally encoded live claim family appears to have a corresponding formal path,
- no obvious unfinished proof markers were found in `MaleyLean/Papers/YangMills`,
- and the end-to-end Yang-Mills workflow check currently succeeds.

It does not automatically mean:

- that an external newer draft of the paper contains nothing beyond this checkout,
- or that the repository's own encoded inventory is impossible to extend.

So the present status is best read as:

- complete relative to the current encoded Yang-Mills inventory,
- not necessarily complete relative to any future or external manuscript revision.

## Live Claim Families

The repository classifies these as the live mathematical proof burden:

- ultraviolet public scope,
- Route 1 lattice gap,
- Lane A sharp-local construction,
- QE3 continuum gap transport,
- endpoint local net.

These are recorded in:

- `MaleyLean/Papers/YangMills/Obligations/ClaimLedger.lean`
- `MaleyLean/Papers/YangMills/Obligations/PaperLedger.lean`
- `MaleyLean/Papers/YangMills/Obligations/Inventory.lean`

## Main Paper-Facing Registers

The theorem and source-facing registries currently include:

- `MaleyLean/Papers/YangMills/Verbatim/TheoremRegister.lean`
- `MaleyLean/Papers/YangMills/Verbatim/DependencySpineSimple.lean`
- `MaleyLean/Papers/YangMills/SourceCrosswalk/Register.lean`
- `MaleyLean/Papers/YangMills/SourceCrosswalk/WitnessRegister.lean`
- `MaleyLean/Papers/YangMills/SourceCrosswalk/ConstructiveWitnessRegister.lean`
- `MaleyLean/Papers/YangMills/SourceCrosswalk/VacuumGapWitnessRegister.lean`
- `MaleyLean/Papers/YangMills/SourceCrosswalk/EndpointWitnessRegister.lean`

These files serve as the clearest local evidence that the manuscript-facing
claim inventory has been translated into repo-visible formal objects.

## Kernel Coverage Highlights

The constructive family is centered in:

- `MaleyLean/Papers/YangMills/Kernel/ConstructiveCore.lean`
- `MaleyLean/Papers/YangMills/Kernel/ConstructiveSemanticBundle.lean`
- `MaleyLean/Papers/YangMills/Kernel/ConstructiveRelationalInterface.lean`
- `MaleyLean/Papers/YangMills/Kernel/ConstructiveExtendAssembleLawPackage.lean`
- `MaleyLean/Papers/YangMills/Kernel/ConstructiveEndpointLawPackage.lean`

The vacuum-gap family is centered in:

- `MaleyLean/Papers/YangMills/Kernel/VacuumGapCore.lean`
- `MaleyLean/Papers/YangMills/Kernel/VacuumGapSemanticBundle.lean`
- `MaleyLean/Papers/YangMills/Kernel/VacuumGapRelationalInterface.lean`
- `MaleyLean/Papers/YangMills/Kernel/VacuumGapTransportRealizeLawPackage.lean`
- `MaleyLean/Papers/YangMills/Kernel/BoundedBaseTransportLawPackage.lean`

The endpoint family is centered in:

- `MaleyLean/Papers/YangMills/Kernel/EndpointCore.lean`
- `MaleyLean/Papers/YangMills/Kernel/EndpointSemanticBundle.lean`
- `MaleyLean/Papers/YangMills/Kernel/EndpointRelationalInterface.lean`
- `MaleyLean/Papers/YangMills/Kernel/EndpointCorrelationLawPackage.lean`
- `MaleyLean/Papers/YangMills/Kernel/GapTransportEndpointLawPackage.lean`

The theorem-facing and cross-heart layers are centered in:

- `MaleyLean/Papers/YangMills/Kernel/CrossHeartLaws.lean`
- `MaleyLean/Papers/YangMills/Kernel/CrossHeartLawObjects.lean`
- `MaleyLean/Papers/YangMills/Kernel/InterHeartCompatibility.lean`
- `MaleyLean/Papers/YangMills/Kernel/TheoremBridgeInterface.lean`
- `MaleyLean/Papers/YangMills/Kernel/TheoremBridgeConsequences.lean`
- `MaleyLean/Papers/YangMills/Kernel/TheoremAssemblyWitness.lean`

The deepest native semantic path is centered in:

- `MaleyLean/Papers/YangMills/Kernel/NativeLawAssembly.lean`
- `MaleyLean/Papers/YangMills/Kernel/NativeInterHeartCompatibility.lean`
- `MaleyLean/Papers/YangMills/Kernel/NativeConstructiveVacuumGapLaw.lean`
- `MaleyLean/Papers/YangMills/Kernel/NativeVacuumGapEndpointLaw.lean`
- `MaleyLean/Papers/YangMills/Kernel/NativeConstructiveEndpointLaw.lean`

and then extended by the native image / factorization / coherence hierarchy.

## Recent Deep-Kernel Improvements

The most recent meaningful refinements were not extra wrappers. They were
kernel-facing improvements to the mathematical story:

- route equalities were turned into named kernel theorems,
- constructive-to-endpoint was made compositional through vacuum-gap,
- general witness theorems were added for the three main cross-heart law
  directions,
- endpoint exactness was rebased onto the endpoint packet theorem and then tied
  more explicitly to the chosen smear / correlate route,
- constructive bounded-base extraction was rebased onto the sharp-local core
  theorem and then tied more explicitly to the chosen sharp-local assembly path.

## Current Verification State

The latest workflow-level check succeeded with:

```text
lake env lean .github\\workflows\\AxiomCheck.lean
```

The deepest Yang-Mills kernel slices touched in the latest pass also rebuilt and
their export statements remained axiom-free.

## Remaining Meaningful Work

At this point, more meaningful work would not come from adding more summary or
alignment scaffolding.

The next real step would require one of:

- a new mathematical statement from the paper that is not yet represented in the
  current encoded inventory,
- a newer manuscript snapshot,
- or a deliberate decision to enrich the encoded inventory beyond what is
  currently registered in the repo.

Without that, additional "formalization progress" would mostly be structural
repackaging rather than new paper verification.
