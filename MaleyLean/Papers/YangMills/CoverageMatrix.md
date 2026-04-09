# Yang-Mills Coverage Matrix

Last updated: 2026-04-09

## Reading Guide

This table summarizes the current local coverage of the Yang-Mills paper as it
is encoded inside this checkout.

The key question is:

"Does this claim family have a clear path from paper-facing registration into
kernel formalization and theorem-facing export?"

## Matrix

| Claim family | Encoded in claim ledger | Verbatim theorem register | Kernel path present | Native / theorem-facing landing | Status |
| --- | --- | --- | --- | --- | --- |
| Ultraviolet public scope | Yes | Yes | Yes | Yes | Covered |
| Route 1 lattice gap | Yes | Yes | Yes | Yes | Covered |
| Lane A sharp-local construction | Yes | Yes | Yes | Yes | Covered |
| QE3 continuum gap transport | Yes | Yes | Yes | Yes | Covered |
| Endpoint local net | Yes | Yes | Yes | Yes | Covered |

## Main Supporting Files

### Claim / manuscript inventory

- `MaleyLean/Papers/YangMills/Obligations/ClaimLedger.lean`
- `MaleyLean/Papers/YangMills/Obligations/PaperLedger.lean`
- `MaleyLean/Papers/YangMills/Obligations/Inventory.lean`

### Verbatim paper register

- `MaleyLean/Papers/YangMills/Verbatim/TheoremRegister.lean`
- `MaleyLean/Papers/YangMills/Verbatim/DependencySpineSimple.lean`

### Constructive kernel

- `MaleyLean/Papers/YangMills/Kernel/ConstructiveCore.lean`
- `MaleyLean/Papers/YangMills/Kernel/ConstructiveSemanticBundle.lean`
- `MaleyLean/Papers/YangMills/Kernel/ConstructiveExtendAssembleLawPackage.lean`

### Vacuum-gap kernel

- `MaleyLean/Papers/YangMills/Kernel/VacuumGapCore.lean`
- `MaleyLean/Papers/YangMills/Kernel/VacuumGapSemanticBundle.lean`
- `MaleyLean/Papers/YangMills/Kernel/VacuumGapTransportRealizeLawPackage.lean`

### Endpoint kernel

- `MaleyLean/Papers/YangMills/Kernel/EndpointCore.lean`
- `MaleyLean/Papers/YangMills/Kernel/EndpointSemanticBundle.lean`
- `MaleyLean/Papers/YangMills/Kernel/EndpointCorrelationLawPackage.lean`

### Cross-heart / theorem-facing kernel

- `MaleyLean/Papers/YangMills/Kernel/CrossHeartLaws.lean`
- `MaleyLean/Papers/YangMills/Kernel/CrossHeartLawObjects.lean`
- `MaleyLean/Papers/YangMills/Kernel/InterHeartCompatibility.lean`
- `MaleyLean/Papers/YangMills/Kernel/TheoremBridgeInterface.lean`
- `MaleyLean/Papers/YangMills/Kernel/TheoremBridgeConsequences.lean`
- `MaleyLean/Papers/YangMills/Kernel/TheoremAssemblyWitness.lean`

### Deep native path

- `MaleyLean/Papers/YangMills/Kernel/NativeLawAssembly.lean`
- `MaleyLean/Papers/YangMills/Kernel/NativeInterHeartCompatibility.lean`
- `MaleyLean/Papers/YangMills/Kernel/NativeConstructiveVacuumGapLaw.lean`
- `MaleyLean/Papers/YangMills/Kernel/NativeVacuumGapEndpointLaw.lean`
- `MaleyLean/Papers/YangMills/Kernel/NativeConstructiveEndpointLaw.lean`

## Local Verdict

Relative to the Yang-Mills inventory encoded in this repository, all currently
registered live claim families appear covered.

No obvious local unfinished markers were found in `MaleyLean/Papers/YangMills`,
and the current workflow-level Yang-Mills verification passes.

## Caveat

This matrix is local-repo-relative.

It answers:

"Is the encoded Yang-Mills paper inventory covered in this checkout?"

It does not answer:

"Does some newer or external paper draft contain additional claims not yet
encoded here?"
