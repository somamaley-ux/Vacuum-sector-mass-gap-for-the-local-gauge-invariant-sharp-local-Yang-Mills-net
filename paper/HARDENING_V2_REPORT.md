# Hardening v2 report

This round targets the three remaining chat-panel blockers identified in the last audit:

1. theorem-local overlap proof for the finite-cap to inductive-union passage;
2. explicit bounded approximation sequence for bounded-base cyclicity / density;
3. kernel seam-locality at the Lane A closure nodes.

## Files edited

- `core/sections/05_laneA.tex`
- `kernel/sections/05_laneA.tex`
- `core/sections/06_qe3_transport.tex`
- `kernel/sections/06_qe3_transport.tex`
- `kernel/sections/02_dependency_spine.tex`
- `companion2.tex`
- `appendices/appendixB_native.tex`
- `companion2_appendices/appendixB_native.tex`
- `companion2_native_appendices/appendixB_native.tex`

## What changed

### 1. Finite-cap -> inductive-union seam is now theorem-local

The proof of Corollary V.11 / Source Corollary 5.76 no longer relies on the compressed sentence that coherent normalization “identifies the same renormalized fields inside every larger cap.”

It now gives an explicit three-step overlap argument:

- equality on overlap words in the bounded and flowed sectors;
- equality on overlap words containing renormalized local generators, via the *same* inverse-flow approximants in both caps and the capwise mixed-channel limit;
- extension from overlap words to the full smaller-cap algebra by linearity.

This argument is written directly in the core, the proof kernel, and the Companion II proof transcription.

### 2. Bounded-base cyclicity now uses an explicit approximation sequence

The proof of Theorem V.13 / Source Theorem 5.77 no longer jumps from capwise approximants to density by a compressed completion sentence.

It now constructs, for a fixed sharp-local positive-time polynomial

- a finite cap containing all generators;
- RP-safe bounded representatives `B_{nu,n} in A_+` for each generator;
- an explicit bounded polynomial sequence `P_n^{bnd}`;
- a telescoping identity for `P_n^{bnd} - P`;
- a cap-dependent norm bound reducing convergence to the individual generator approximations.

Density in the full Hilbert space is then proved by a two-stage epsilon argument:

- first approximate an arbitrary Hilbert vector by a positive-time sharp-local polynomial class;
- then approximate that class by the bounded sequence.

The centered-sector statement is also tightened from a raw algebraic `span = Omega^perp` claim to the mathematically correct

- `closed linear span = Omega^perp`.

This correction is propagated to the QE3 density corollary.

### 3. Kernel now states seam-locality explicitly

The kernel dependency-spine section now says, in theorem-facing prose, that the Lane A overlap proof and the bounded approximating sequence are carried locally in the kernel itself, with the companions serving as proof-home verification rather than hidden dependencies.

## Audit-facing effect

These edits are designed to remove the two remaining proof-local compression objections at the full-union state and bounded-base density seams, while also making the kernel self-sufficient at those nodes.

## Build note

No TeX engine is available in this environment, so the deliverable is source-only. The edited bundle is prepared for recompilation in a TeX environment.
