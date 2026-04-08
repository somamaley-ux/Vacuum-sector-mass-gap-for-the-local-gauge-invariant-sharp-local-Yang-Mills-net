# Gauge Constraint Dynamics Lean Status

## Current state

The manuscript

`Admissibility and the Structural Origin of Gauge and Constraint Dynamics`

is now fully integrated in the Lean workspace to the repo's no-axiom standard.

That means the paper's current formal surface and its present support layers are
axiom-free under the repo's audit workflow.

## What is in Lean

The current Lean surface is centered in:

- `MaleyLean/Papers/GaugeConstraintDynamics/PaperStatements.lean`
- `MaleyLean/Papers/GaugeConstraintDynamics/SymplecticGeometry.lean`
- `MaleyLean/Papers/GaugeConstraintDynamics/CanonicalGR.lean`
- `MaleyLean/Papers/GaugeConstraintDynamics/EverettDecoherence.lean`
- `MaleyLean/Papers/GaugeConstraintDynamics/EverettSelectors.lean`
- `MaleyLean/Papers/GaugeConstraintDynamics/EverettToyModel.lean`

with audit coverage in:

- `Checks/Axiom/GaugeConstraintDynamicsAxiomCheck.lean`
- `Checks/Axiom/SymplecticGeometryAxiomCheck.lean`
- `Checks/Axiom/CanonicalGRAxiomCheck.lean`
- `Checks/Axiom/EverettDecoherenceAxiomCheck.lean`
- `Checks/Axiom/EverettSelectorsAxiomCheck.lean`
- `Checks/Axiom/EverettToyModelAxiomCheck.lean`

Together, these give the project:

- a Stage I surface for involutive admissible-redescription structure
- a Stage II surface for kernel inclusion, characteristic identification, and coisotropic forcing
- a Stage III surface for local generator span, weak first-class closure, and second-class exclusion
- a Stage IV surface for multiplier-type Hamiltonian rigidity
- a geometry-facing support library for local presymplectic structure, characteristic identification, coisotropic witnesses, normal-form charts, and second-class exclusion
- a canonical-GR realization layer for weak first-class closure and multiplier rigidity over a constrained Hamiltonian system
- a paper-facing application layer for collapse / Everett trilemmas and terminal selector exhaustion
- a reusable Everett selector / branching substrate beneath that paper-facing layer
- a decoherence-facing pointer/coarse-graining layer beneath the selector substrate
- a concrete finite toy model witnessing factorization-dependent branch extraction
- a concrete fine-vs-coarse pointer-record witness for decoherence-level dependence
- a bundled verified-core theorem for the manuscript's structural spine

## What changed in the integration

The new Lean layer follows the repo's established pattern for paper integration:
it packages the manuscript's theorem surface as explicit hypothesis-driven declarations
rather than importing hidden axioms or pretending that full low-level symplectic,
ADM-GR, or Hilbert-space machinery is already internalized.

This means the paper is now integrated honestly at the same certified paper-facing
level as the other manuscript modules in the repo, with its current derived
support layers also carried axiom-free.

## Main files

- `papers/gauge_constraint_dynamics/main.tex`
- `papers/gauge_constraint_dynamics/main.pdf`
- `papers/gauge_constraint_dynamics/README.md`
- `MaleyLean/Papers/GaugeConstraintDynamics/PaperStatements.lean`
- `MaleyLean/Papers/GaugeConstraintDynamics/SymplecticGeometry.lean`
- `MaleyLean/Papers/GaugeConstraintDynamics/CanonicalGR.lean`
- `MaleyLean/Papers/GaugeConstraintDynamics/EverettDecoherence.lean`
- `MaleyLean/Papers/GaugeConstraintDynamics/EverettSelectors.lean`
- `MaleyLean/Papers/GaugeConstraintDynamics/EverettToyModel.lean`
- `Checks/Axiom/GaugeConstraintDynamicsAxiomCheck.lean`
- `Checks/Axiom/SymplecticGeometryAxiomCheck.lean`
- `Checks/Axiom/CanonicalGRAxiomCheck.lean`
- `Checks/Axiom/EverettDecoherenceAxiomCheck.lean`
- `Checks/Axiom/EverettSelectorsAxiomCheck.lean`
- `Checks/Axiom/EverettToyModelAxiomCheck.lean`
- `reports/support_maps/gauge_constraint_dynamics_support_map.txt`
- `reports/audits/gauge_constraint_dynamics_axiom_audit.txt`

## Verification

The dedicated module and axiom check build successfully, and the root
`MaleyLean` / `Checks` targets still build with the new import surface included.

The current paper-facing theorem surface is axiom-free, and the current
geometry, canonical-GR, selector, toy-model, and decoherence support modules
for this paper are axiom-free as well.

## Honest boundary

What is certified here is the manuscript-facing structural theorem layer together
with the support layers currently used to derive it in this repo.

What is not yet internalized in full detail is:

- a low-level symplectic manifold library with explicit forms, kernels, and local charts
- a full ADM/canonical-GR derivation stack beyond the current constrained-Hamiltonian realization layer
- a full Hilbert-space dynamics and decoherence formalization

So the current result should be read as:

- fully formalized to the repo's no-axiom standard
- fully derived relative to the support layers currently internalized here
- not yet a complete bottom-to-top foundational library for every mathematical
  object named in the manuscript

## Best next move

If we keep pushing this paper, the most valuable next step is now integration
and refinement rather than opening a brand-new substrate track:

1. connect the geometry and canonical-GR layers with a tighter ADM-style bridge
2. enrich the decoherence toy layer into an explicit environment-coupling model
3. replace more paper-facing hypotheses with internal support theorems as the substrate grows
