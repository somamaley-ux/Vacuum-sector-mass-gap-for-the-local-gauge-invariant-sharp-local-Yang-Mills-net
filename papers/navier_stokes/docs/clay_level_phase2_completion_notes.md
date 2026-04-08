# Clay-level closure plan - Phase 2 completion notes

Phase 2 of the updated clay-level closure plan is now integrated into the manuscript source.

## Objective completed
Derive the minimum admissibility / intelligibility / identity content directly from the structure of the maximal classical periodic solution, using theorem-local PDE facts rather than corpus slogans.

## Main source changes
- Added a new Part III subsection:
  - `PDE-native admissibility packet on the maximal classical interval`
- Added theorem-local packet:
  - `19C` `\label{thm:pde-native-admissibility-maximal-interval}`
  - `19D` `\label{thm:restart-consistency-same-object-persistence}`
  - `19E` `\label{cor:pre-horizon-slice-reentry}` (while preserving the legacy label `lem:propagation-standing-positive-slices` for downstream references)
  - `19F` `\label{lem:finite-horizon-witness}`
- Rewrote the realized-lineage standing packet proofs so `ST4`, `20C.2`, and `20C` explicitly depend on the new PDE-native packet.
- Updated front matter:
  - theorem map,
  - glossary / PDE crosswalk,
  - compressed proof spine,
  - denial map.
- Expanded Appendix F with a dedicated updated-plan Phase-2 audit subsection and updated live-node / referee-matrix references.
- Updated `README.md` to reflect Phase 0 + Phase 1 + Phase 2 status.

## Mathematical effect of the phase
The manuscript now states locally that:
- the realized maximal classical periodic solution has fixed reference on `[0,T_*(x))`,
- smooth restarts from interior times reproduce the same realized lineage on overlap,
- every smooth pre-horizon slice re-enters the same admitted carrier and is standing-positive there,
- any finite-horizon failure is already witnessed before the horizon by divergence of an in-scope continuation norm.

## Why this matters for the hostile objection
This phase removes the need for `ST4`, `ST5`, or the continuation-failure dichotomy to smuggle global regularity into their pre-horizon standing claims. The pre-horizon burden is now visibly local-in-time and comes from the theorem-local classical realization packet plus overlap uniqueness.
