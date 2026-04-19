# Yang--Mills Full Native Package Boundary

Standalone Lean snapshot for the Yang--Mills slice of the wider `MaleyLean`
project, aligned with the current manuscript-facing native package boundary.

## Main result

The main win in this repository is not just a theorem register or a packaging
cleanup. The real advance is that the four highest-risk analytic seams in the
current Yang--Mills manuscript-facing route are now mechanized much more
explicitly and much more locally than before.

Those four critical seams are:

- the QE3 density / graph-core handoff
- the dyadic-to-continuous-time OS upgrade
- the continuum transport / sharp-gap bridge
- the Section 8 endpoint / admissibility bridge

In the current export, those seams are no longer left as vague route-level
transitions. They are exposed through reduced payloads, source-grounded
projections, proof-home projections, route recoveries, and theorem-level
reconstructions inside the standalone Lean package.

For the nonlocal endpoint manuscript specifically, the standalone export now
also reflects the paper's section-level theorem posture much more closely:

- Section 4's frozen theorem-scope extended-support class is represented as a
  fixed support-and-label class with explicit support and deformation notions
- Section 7's global-form recovery problem is represented as a same-local-shadow
  versus different-global-form sector distinction problem
- Section 8's endpoint bridge is represented as a scope-faithful completion and
  admissibility bridge over the unchanged local vacuum theory

That means the remaining abstraction is no longer "the hard seams are still
informal." Those seams are now source-grounded, isolated, reconstructed, and
promoted into named theorem surfaces. What remains more abstract is the final
paper-faithful packaging of the theorem-scope class and the most manuscript-
shaped Section 8 bridge presentation.

That is the central human-facing message of this repo: the decisive seam logic
is now isolated, named, crosswalked back to source ownership, and compiled into
an axiom-free manuscript-facing package boundary.

## Start here

If you are new to this repository, the naming split is:

- `MaleyLean` is the Lean package name
- `YangMills` is the paper/topic packaged in this standalone export

The main entry points are:

- `Main.lean`
  the single canonical standalone entry point; it loads
  `MaleyLean.YangMillsFullManuscriptNativePackage`
- `BundleMain.lean`
  optional broader bundle that loads the full native package and its summary
  surface together

If you want one file to inspect first, start with `Main.lean`.

## Contents

- `MaleyLean/`
  standalone Lean dependency closure for the current Yang--Mills manuscript
  package boundary
- `Checks/Axiom/YangMillsFullManuscriptNativePackageAxiomCheck.lean`
  dedicated top-package axiom audit entry point
- `paper/`
  bundled manuscript source tree, source archive, and supplied PDFs
- `reports/audits/yang_mills_submission_layer_audit_2026-04-15.md`
  referee-facing audit note for the current top package boundary
- `reports/support_maps/yang_mills_support_map.txt`
  manuscript-to-Lean support map
- `reports/status/yang_mills_status.md`
  human-readable status note
- `reports/submission/`
  editor/referee-facing submission support notes

## Build

This project uses Lean `v4.28.0` via `lean-toolchain`.

Build the extracted project with:

```text
lake build
```

Build the single canonical paper entry point with:

```text
lake env lean Main.lean
```

Run the dedicated top-package axiom check with:

```text
lake env lean Checks\\Axiom\\YangMillsFullManuscriptNativePackageAxiomCheck.lean
```

## Scope

This repo packages the current strongest manuscript-facing Yang--Mills native
boundary available in the source development: the constructive, vacuum-gap, and
endpoint theorem-object, proof-home, law-atom, primitive, certificate, trace,
and construction-stage layers tied together in
`YangMillsFullManuscriptNativePackageExportStatement`.

Most importantly, that package now foregrounds the analytical mechanization of
the four critical seams listed above, so the hardest manuscript transitions are
not only asserted globally but tracked through explicit local bridge objects and
reconstruction paths.

It also bundles the current manuscript tree rooted in `core.tex`,
`companion1.tex`, `companion2.tex`, and `companion3.tex`, together with the
anonymized source archive, anonymized companion PDFs, and the proof-kernel
extraction materials.

This repository should be read as a strong manuscript-facing formal companion to
the current Yang--Mills submission boundary. It is not yet a claim that every
underlying analytic Yang--Mills argument has already been fully internalized as
foundational Lean analysis.
