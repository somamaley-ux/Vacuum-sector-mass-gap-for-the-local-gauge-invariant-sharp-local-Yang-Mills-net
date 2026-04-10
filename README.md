# Yang--Mills Native Boundary

Standalone Lean snapshot for the deeper native Yang--Mills boundary aligned
with the hardened source suite.

## Contents

- `MaleyLean/`
  standalone Lean dependency closure for the native constructive, vacuum-gap,
  endpoint, and cross-heart law boundary
- `Checks/Axiom/YangMillsDeepNativeBoundaryAxiomCheck.lean`
  dedicated deep-native axiom audit entry point
- `paper/`
  bundled manuscript source tree, original source archive, and supplied PDFs
- `reports/audits/yang_mills_axiom_audit.txt`
  human-readable audit note
- `reports/support_maps/yang_mills_support_map.txt`
  manuscript-to-Lean support map
- `reports/status/yang_mills_status.md`
  human-readable status note

## Build

This project uses Lean `v4.28.0` via `lean-toolchain`.

Build the extracted project with:

```text
lake build
```

Run the dedicated deep-native axiom check with:

```text
lake env lean Checks\\Axiom\\YangMillsDeepNativeBoundaryAxiomCheck.lean
```

## Scope

This repo packages the current deeper native Yang--Mills boundary:
the constructive, vacuum-gap, and endpoint semantic/relational bundles;
the theorem/native alignment layer; the native law and cross-heart law
consequence layer; and the canonical verified payload exported over the route
interfaces already encoded in the repository.

It also bundles the current manuscript tree rooted in `core.tex`,
`companion1.tex`, `companion2.tex`, and `companion3.tex`, together with an
anonymized source archive, anonymized companion PDFs, and the proof-kernel
extraction materials.

It should be read as a faithful formal companion to the manuscript's deeper
native theorem layer, not merely to the older structural routing surface.
The exported native boundary is still parameterized over route/core objects and
semantic-bundle data, so this repo should not yet be described as one fully
closed canonical proposition for the complete analytic Yang--Mills manuscript.
