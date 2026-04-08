# Repository Reorganization Plan

## Goal

Keep the Lean source tree readable as the repository grows by separating:

- shared kernel and reusable building blocks
- primitive and structural layers
- paper-specific developments
- generated checks, reports, and scratch artifacts

The current flat layout under `MaleyLean/` works for a small codebase, but it
is already mixing several different responsibilities:

- foundational modules like `Foundation`, `Core`, `Transport`, `Witness`
- reusable structural machinery like `Standing*`, `No*`, `Refinement*`
- generic paper-facing bundles like `PaperStatements`
- paper-specific clusters like `NavierStokes*`, `Godel*`, `StandardModel*`

This plan keeps imports manageable without forcing a risky one-shot rewrite.

## Recommended Target Layout

```text
MaleyLean/
  Core/
    Foundation.lean
    Core.lean
    Boundary.lean
    Failure.lean
    Composition.lean
    ClosurePropagation.lean
    Equivalence.lean
    Irrecoverability.lean
    Transport.lean
    Witness.lean
    TheoremRegister.lean
    StatusKernel.lean
  Primitives/
    Standing/
    Collapse/
    Refinement/
    Target/
    NoRepair/
    Interfaces/
    Constructive/
  Papers/
    Generic/
    ATS/
    Ametric/
    Godel/
    NavierStokes/
    StandardModel/
    Electroweak/
    Closure/
    Meta/
```

The top-level file `MaleyLean.lean` should remain as a compatibility facade
that imports the new module locations.

## Non-Source Layout

The repository root is also carrying too many generated and workflow files.
These should move out of the top level.

```text
checks/
  axiom/
reports/
  audits/
  support_maps/
  status/
tmp/
  lean/
  drafts/
```

Suggested moves:

- `*AxiomCheck.lean` -> `checks/axiom/`
- `*_axiom_audit.txt` -> `reports/audits/`
- `*_support_map.txt` and `*_support_gap.txt` -> `reports/support_maps/`
- `*_status.md` -> `reports/status/`
- `Tmp*.lean`, `.tmp_*`, `*.olean.tmp.*` -> `tmp/lean/` or ignored scratch
- completed manuscript directories like `papers/navier_stokes` and
  `papers/godel` -> keep under `papers/` so the repo reads as canonical rather
  than provisional

## Concrete Module Mapping

### 1. Core

These look like shared infrastructure and should move first because many other
files depend on them.

```text
MaleyLean/Foundation.lean                 -> MaleyLean/Core/Foundation.lean
MaleyLean/Core.lean                       -> MaleyLean/Core/Core.lean
MaleyLean/Boundary.lean                   -> MaleyLean/Core/Boundary.lean
MaleyLean/Failure.lean                    -> MaleyLean/Core/Failure.lean
MaleyLean/Composition.lean                -> MaleyLean/Core/Composition.lean
MaleyLean/ClosurePropagation.lean         -> MaleyLean/Core/ClosurePropagation.lean
MaleyLean/Equivalence.lean                -> MaleyLean/Core/Equivalence.lean
MaleyLean/Irrecoverability.lean           -> MaleyLean/Core/Irrecoverability.lean
MaleyLean/ChainComposition.lean           -> MaleyLean/Core/ChainComposition.lean
MaleyLean/ChainIrrecoverability.lean      -> MaleyLean/Core/ChainIrrecoverability.lean
MaleyLean/Transport.lean                  -> MaleyLean/Core/Transport.lean
MaleyLean/Witness.lean                    -> MaleyLean/Core/Witness.lean
MaleyLean/TheoremRegister.lean            -> MaleyLean/Core/TheoremRegister.lean
MaleyLean/StatusKernel.lean               -> MaleyLean/Core/StatusKernel.lean
MaleyLean/StabilizationCheckpoint.lean    -> MaleyLean/Core/StabilizationCheckpoint.lean
MaleyLean/InvariantBundle.lean            -> MaleyLean/Core/InvariantBundle.lean
MaleyLean/EnvelopeInvariants.lean         -> MaleyLean/Core/EnvelopeInvariants.lean
MaleyLean/ImpossibilityHarness.lean       -> MaleyLean/Core/ImpossibilityHarness.lean
```

### 2. Primitives

These are reusable structural components, not tied to one paper.

#### Standing

```text
StandingCarriesMetricFreedom.lean         -> Primitives/Standing/CarriesMetricFreedom.lean
StandingClassifierBridge.lean             -> Primitives/Standing/ClassifierBridge.lean
StandingConservation.lean                 -> Primitives/Standing/Conservation.lean
StandingDeterminacy.lean                  -> Primitives/Standing/Determinacy.lean
StandingEmergence.lean                    -> Primitives/Standing/Emergence.lean
StandingEmergenceBase.lean                -> Primitives/Standing/EmergenceBase.lean
StandingEmergenceConstructive.lean        -> Primitives/Standing/EmergenceConstructive.lean
StandingMetricSeparation.lean             -> Primitives/Standing/MetricSeparation.lean
StandingPositiveSideCollapse.lean         -> Primitives/Standing/PositiveSideCollapse.lean
StandingPositiveSideNoGap.lean            -> Primitives/Standing/PositiveSideNoGap.lean
StandingPreservation.lean                 -> Primitives/Standing/Preservation.lean
StandingRefinement.lean                   -> Primitives/Standing/Refinement.lean
```

#### Collapse and Split

```text
AmetricBoundary.lean                      -> Primitives/Collapse/AmetricBoundary.lean
AmetricCollapseTheorem.lean               -> Primitives/Collapse/AmetricCollapseTheorem.lean
AuxiliaryDataCollapse.lean                -> Primitives/Collapse/AuxiliaryDataCollapse.lean
PositiveRefinementCollapse.lean           -> Primitives/Collapse/PositiveRefinementCollapse.lean
PositiveRefinementSplit.lean              -> Primitives/Collapse/PositiveRefinementSplit.lean
SameSideSplit.lean                        -> Primitives/Collapse/SameSideSplit.lean
SplitCollapse.lean                        -> Primitives/Collapse/SplitCollapse.lean
```

#### Refinement and Target Routing

```text
PositiveSideEffectiveness.lean            -> Primitives/Refinement/PositiveSideEffectiveness.lean
PositiveSideInterfaceDerivation.lean      -> Primitives/Refinement/PositiveSideInterfaceDerivation.lean
RedescriptionAction.lean                  -> Primitives/Refinement/RedescriptionAction.lean
RedescriptionRefinementBridge.lean        -> Primitives/Refinement/RedescriptionRefinementBridge.lean
RefinementToTarget.lean                   -> Primitives/Refinement/RefinementToTarget.lean
SameSideEffectiveRefinement.lean          -> Primitives/Refinement/SameSideEffectiveRefinement.lean
SameSideRefinementBridge.lean             -> Primitives/Refinement/SameSideRefinementBridge.lean
ScopedTransport.lean                      -> Primitives/Refinement/ScopedTransport.lean
TargetEnvelope.lean                       -> Primitives/Target/Envelope.lean
TargetToRedescription.lean                -> Primitives/Target/ToRedescription.lean
AdmissibilityRelevance.lean               -> Primitives/Target/AdmissibilityRelevance.lean
InteriorUniqueness.lean                   -> Primitives/Target/InteriorUniqueness.lean
```

#### Interfaces and Negation Layers

```text
Bivalence.lean                            -> Primitives/Interfaces/Bivalence.lean
BivalenceInterface.lean                   -> Primitives/Interfaces/BivalenceInterface.lean
BivalenceUniqueness.lean                  -> Primitives/Interfaces/BivalenceUniqueness.lean
NoCarriers.lean                           -> Primitives/NoRepair/NoCarriers.lean
NoDeferredRepair.lean                     -> Primitives/NoRepair/NoDeferredRepair.lean
NoFiniteRepair.lean                       -> Primitives/NoRepair/NoFiniteRepair.lean
NoGenerators.lean                         -> Primitives/NoRepair/NoGenerators.lean
NoGeneratorsConstructive.lean             -> Primitives/Constructive/NoGenerators.lean
NoInformationInFailureRegion.lean         -> Primitives/NoRepair/NoInformationInFailureRegion.lean
NoPostSelectionRepair.lean                -> Primitives/NoRepair/NoPostSelectionRepair.lean
NoRepair.lean                             -> Primitives/NoRepair/NoRepair.lean
NoSameActRepair.lean                      -> Primitives/NoRepair/NoSameActRepair.lean
NoSameScopePromotion.lean                 -> Primitives/NoRepair/NoSameScopePromotion.lean
NoSilentRedescription.lean                -> Primitives/NoRepair/NoSilentRedescription.lean
NoStagedRepair.lean                       -> Primitives/NoRepair/NoStagedRepair.lean
```

### 3. Papers

Paper-specific modules should be grouped by project rather than by suffix.

#### Generic paper-facing bundles

```text
PaperStatements.lean                      -> Papers/Generic/PaperStatements.lean
PaperStatementsConstructive.lean          -> Papers/Generic/PaperStatementsConstructive.lean
ClosurePaperStatements.lean               -> Papers/Closure/PaperStatements.lean
UniquenessPaperStatements.lean            -> Papers/Generic/UniquenessPaperStatements.lean
BivalentTrajectoryPaperStatements.lean    -> Papers/Generic/BivalentTrajectoryPaperStatements.lean
EquivalenceExhaustion.lean                -> Papers/Generic/EquivalenceExhaustion.lean
EquivalenceExhaustionPaperStatements.lean -> Papers/Generic/EquivalenceExhaustionPaperStatements.lean
```

#### ATS / Ametric / Godel / Meta

```text
ATSPaperStatements.lean                   -> Papers/ATS/PaperStatements.lean
AmetricPaperStatements.lean               -> Papers/Ametric/PaperStatements.lean
GodelPaperStatements.lean                 -> Papers/Godel/PaperStatements.lean
GodelVerbatimRegister.lean                -> Papers/Godel/VerbatimRegister.lean
EmpiricalCompletenessCore.lean            -> Papers/Meta/EmpiricalCompleteness/Core.lean
EmpiricalCompletenessPaperStatements.lean -> Papers/Meta/EmpiricalCompleteness/PaperStatements.lean
ClaimModalityPaperCore.lean               -> Papers/Meta/ClaimModality/Core.lean
ClaimModalityPaperStatements.lean         -> Papers/Meta/ClaimModality/PaperStatements.lean
MetaNecessityAdmissibilityCore.lean       -> Papers/Meta/NecessityAdmissibility/Core.lean
MetaNecessityAdmissibilityPaperStatements.lean
                                            -> Papers/Meta/NecessityAdmissibility/PaperStatements.lean
LorentzianKinematicConfirmationCore.lean  -> Papers/Meta/LorentzianKinematicConfirmation/Core.lean
LorentzianKinematicConfirmationPaperStatements.lean
                                            -> Papers/Meta/LorentzianKinematicConfirmation/PaperStatements.lean
MathClosurePaperStatements.lean           -> Papers/Closure/MathClosurePaperStatements.lean
PrimitiveToPeriodicLocalTheory.lean       -> Papers/Meta/PrimitiveToPeriodicLocalTheory.lean
```

#### Navier-Stokes

This family is already large enough to deserve its own nested structure.

```text
NavierStokesPrimitiveCore.lean            -> Papers/NavierStokes/Primitive/Core.lean
NavierStokesPrimitiveBridge.lean          -> Papers/NavierStokes/Primitive/Bridge.lean
NavierStokesPrimitiveNoBlowup.lean        -> Papers/NavierStokes/Primitive/NoBlowup.lean
NavierStokesQuotientFactorization.lean    -> Papers/NavierStokes/Primitive/QuotientFactorization.lean
NavierStokesContinuationBoundary.lean     -> Papers/NavierStokes/Continuation/Boundary.lean
NavierStokesHorizonCollapse.lean          -> Papers/NavierStokes/Continuation/HorizonCollapse.lean
NavierStokesRestartTransport.lean         -> Papers/NavierStokes/Continuation/RestartTransport.lean
NavierStokesMaximalLineageClosure.lean    -> Papers/NavierStokes/Continuation/MaximalLineageClosure.lean
NavierStokesPDEObligationRegister.lean    -> Papers/NavierStokes/Obligations/Register.lean
NavierStokesPDEObligationInventory.lean   -> Papers/NavierStokes/Obligations/Inventory.lean
NavierStokesPaperObligationLedger.lean    -> Papers/NavierStokes/Obligations/PaperLedger.lean
NavierStokesSectionTheoremLedger.lean     -> Papers/NavierStokes/Obligations/SectionTheoremLedger.lean
NavierStokesDraftClaimRegister.lean       -> Papers/NavierStokes/Verbatim/DraftClaimRegister.lean
NavierStokesVerbatimSubsectionRegister.lean
                                            -> Papers/NavierStokes/Verbatim/SubsectionRegister.lean
NavierStokesVerbatimTheoremRegister.lean  -> Papers/NavierStokes/Verbatim/TheoremRegister.lean
NavierStokesVerbatimDependencySpineSimple.lean
                                            -> Papers/NavierStokes/Verbatim/DependencySpineSimple.lean
NavierStokesVortexStretchingNonLoadBearing.lean
                                            -> Papers/NavierStokes/Surface/VortexStretchingNonLoadBearing.lean
NavierStokesNoHiddenScopeChange.lean      -> Papers/NavierStokes/Surface/NoHiddenScopeChange.lean
NavierStokesPaperSurfaceSummaryClean.lean -> Papers/NavierStokes/Surface/SummaryClean.lean
```

#### Standard Model and nearby physics modules

The Standard Model area should be organized as one paper family with subareas.

```text
StandardModelStructuralPaperStatements.lean
                                            -> Papers/StandardModel/Structural/PaperStatements.lean
StandardModelStructuralMetaClosureStatements.lean
                                            -> Papers/StandardModel/Structural/MetaClosureStatements.lean
StandardModelSupportPaperStatements.lean   -> Papers/StandardModel/Support/PaperStatements.lean
StandardModelDerivedWitnessBundle.lean     -> Papers/StandardModel/Derived/WitnessBundle.lean
StandardModelL1SupportBundle.lean          -> Papers/StandardModel/Support/L1SupportBundle.lean
StandardModelUmbrellaVerifiedCore.lean     -> Papers/StandardModel/Core/UmbrellaVerifiedCore.lean
StandardModelCurrentCertifiedSurface.lean  -> Papers/StandardModel/Surface/CurrentCertifiedSurface.lean
```

Electroweak and flavor-related papers can then sit nearby under a shared
physics umbrella.

```text
YukawaMass*.lean                           -> Papers/Electroweak/YukawaMass/
EMCoupling*.lean                           -> Papers/Electroweak/EMCoupling/
AnomalyYukawa*.lean                        -> Papers/Electroweak/AnomalyYukawa/
ChargedCurrent*.lean                       -> Papers/Electroweak/ChargedCurrent/
FCNC*.lean                                 -> Papers/Electroweak/FCNC/
Hypercharge*.lean                          -> Papers/Electroweak/Hypercharge/
LongitudinalGoldstone*.lean                -> Papers/Electroweak/LongitudinalGoldstone/
NeutrinoMixing*.lean                       -> Papers/Electroweak/NeutrinoMixing/
Rephasing*.lean                            -> Papers/Electroweak/Rephasing/
UnitaryMixing*.lean                        -> Papers/Electroweak/UnitaryMixing/
QCDCPodd*.lean                             -> Papers/Electroweak/QCDCPodd/
```

Within each family, use a stable internal convention:

- `Core.lean`
- `Derived.lean`
- `Equivalence.lean`
- `Collapse.lean`
- `PaperStatements.lean`
- `DerivedPaperStatements.lean`

That is easier to scan than repeating the paper name on every file.

## Import Strategy

Do not switch every import at once. Use a staged migration.

### Stage 1: Create new directories and move files in small batches

Update the moved modules to their new names, for example:

```lean
-- before
import MaleyLean.NavierStokesPrimitiveCore

-- after
import MaleyLean.Papers.NavierStokes.Primitive.Core
```

### Stage 2: Keep compatibility shims

For each moved file, keep a thin compatibility file at the old path:

```lean
import MaleyLean.Papers.NavierStokes.Primitive.Core
```

This lets the rest of the repository compile while you migrate imports
incrementally.

### Stage 3: Introduce aggregator modules

Add new umbrella modules that reflect the structure:

```text
MaleyLean/Core.lean
MaleyLean/Primitives.lean
MaleyLean/Papers.lean
MaleyLean/Papers/NavierStokes.lean
MaleyLean/Papers/StandardModel.lean
```

Then `MaleyLean.lean` can become a short curated facade instead of a giant list
of direct leaf imports.

### Stage 4: Remove shims after import cleanup

Once all internal imports have switched to the new names, delete the old-path
shim modules.

## Recommended Execution Order

1. Move non-source root clutter into `checks/`, `reports/`, and `tmp/`.
   This gives immediate usability improvement with almost no Lean risk.
2. Reorganize the Navier-Stokes family under `Papers/NavierStokes/`.
   It is the clearest large cluster and gives the biggest tree-size win.
3. Reorganize Standard Model and the electroweak family.
4. Move shared structural modules into `Core/` and `Primitives/`.
5. Shorten `MaleyLean.lean` into curated umbrella imports.
6. Remove compatibility shims only after the tree has settled.

## Suggested Naming Rules Going Forward

- If a module is reusable across more than one paper, it does not belong under
  `Papers/`.
- If a module exists only to package manuscript-facing theorems, it belongs
  under the relevant paper folder, usually in `PaperStatements` or `Surface`.
- Avoid adding new leaf files directly under `MaleyLean/`.
- Prefer nested names like `MaleyLean.Papers.NavierStokes.Verbatim.TheoremRegister`
  over flat names like `MaleyLean.NavierStokesVerbatimTheoremRegister`.
- Keep old names only as temporary shims during migration.

## First Practical Refactor

If starting today, the lowest-risk first patch would be:

1. Create `checks/`, `reports/`, and `tmp/` folders and move root clutter.
2. Create `MaleyLean/Papers/NavierStokes/`.
3. Move only the Navier-Stokes modules there.
4. Leave old `NavierStokes*.lean` files as shim imports.
5. Update `README.md` to point to the new Navier-Stokes paths.

That gives a visible improvement immediately without forcing the whole
repository through a large synchronized rename.
