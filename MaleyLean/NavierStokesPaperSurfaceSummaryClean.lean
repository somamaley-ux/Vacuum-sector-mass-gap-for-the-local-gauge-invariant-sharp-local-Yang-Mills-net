import MaleyLean.NavierStokesVerbatimSubsectionRegister
import MaleyLean.NavierStokesVerbatimTheoremRegister
import MaleyLean.NavierStokesVerbatimDependencySpineSimple
import MaleyLean.NavierStokesVortexStretchingNonLoadBearing

namespace MaleyLean

/--
Top-level manuscript-facing summary surface for the Navier--Stokes bundle.

This module re-exports the final cleaned manuscript layers:
- verbatim subsection register
- verbatim theorem register
- verbatim dependency spine
- vortex-stretching non-load-bearing boundary
-/
theorem NavierStokesPaperSurfaceSummaryCleanStatement :
  (verbatim_entry_support_kind .carrierToLineageBindingCommitment = .structurallyCertified /\
   verbatim_entry_support_kind .standingIntelligibilityPacketInternalizedAtFixedPeriodicScope = .structurallyCertified /\
   verbatim_entry_support_kind .constructiveDiagnosticBranchForcingFromBreakdownWitnesses = .structurallyCertified /\
   verbatim_entry_support_kind .constructiveSingularCandidateExtraction = .structurallyCertified /\
   verbatim_entry_support_kind .noSecondSameScopeSingularityGate = .structurallyCertified /\
   verbatim_entry_support_kind .noCompetingSameScopeContinuationGates = .structurallyCertified /\
   verbatim_entry_support_kind .quotientVisibleVsIllicitSingularity = .structurallyCertified /\
   verbatim_entry_support_kind .transferFaithfulnessLocalClassicalContinuation = .structurallyCertified /\
   verbatim_entry_support_kind .pdeNativeAdmissibilityPacketOnTheMaximalClassicalInterval = .structurallyCertified /\
   verbatim_entry_support_kind .noAdmissibleSameScopeSingularityGateRemains = .structurallyCertified) /\
  (verbatim_theorem_support_kind .standingQuotientFutureBehaviorQuotient = .structurallyCertified /\
   verbatim_theorem_support_kind .noCompetingSameScopeContinuationGates = .structurallyCertified /\
   verbatim_theorem_support_kind .noSecondSameScopeSingularityGate = .structurallyCertified /\
   verbatim_theorem_support_kind .quotientVisibleVsIllicitSingularity = .structurallyCertified /\
   verbatim_theorem_support_kind .structuralRegularityOnTheCertifiedPeriodicCarrier = .structurallyCertified /\
   verbatim_theorem_support_kind .transferFaithfulnessLocalClassicalContinuation = .structurallyCertified /\
   verbatim_theorem_support_kind .constructiveDiagnosticBranchForcingFromBreakdownWitnesses = .structurallyCertified /\
   verbatim_theorem_support_kind .constructiveSingularCandidateExtraction = .structurallyCertified /\
   verbatim_theorem_support_kind .noIllicitSingularImage = .structurallyCertified /\
   verbatim_theorem_support_kind .noQuotientVisibleSingularImage = .structurallyCertified /\
   verbatim_theorem_support_kind .transferImpossibilityNoSingularImageOfTheUniqueAdmissibleInterior = .structurallyCertified) /\
  (verbatim_theorem_is_structurally_closed_simple .standingQuotientFutureBehaviorQuotient /\
   verbatim_theorem_is_structurally_closed_simple .noCompetingSameScopeContinuationGates /\
   verbatim_theorem_is_structurally_closed_simple .noSecondSameScopeSingularityGate /\
   verbatim_theorem_is_structurally_closed_simple .quotientVisibleVsIllicitSingularity /\
   verbatim_theorem_is_structurally_closed_simple .structuralRegularityOnTheCertifiedPeriodicCarrier /\
   verbatim_theorem_is_structurally_closed_simple .transferFaithfulnessLocalClassicalContinuation /\
   verbatim_theorem_is_structurally_closed_simple .constructiveDiagnosticBranchForcingFromBreakdownWitnesses /\
   verbatim_theorem_is_structurally_closed_simple .constructiveSingularCandidateExtraction /\
   verbatim_theorem_is_structurally_closed_simple .noIllicitSingularImage /\
   verbatim_theorem_is_structurally_closed_simple .noQuotientVisibleSingularImage /\
   verbatim_theorem_is_structurally_closed_simple .transferImpossibilityNoSingularImageOfTheUniqueAdmissibleInterior) /\
  (verbatim_entry_support_kind .pointwiseVortexStretchingGateCollapse = .namedFailureBoundary) /\
  (verbatim_theorem_support_kind .pointwiseVortexStretchingGateCollapse = .namedFailureBoundary) /\
  (verbatim_theorem_is_named_failure_boundary_simple .pointwiseVortexStretchingGateCollapse) /\
  (forall {State Time Witness Candidate Quantity : Type}
      (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity),
      vortex_stretching_cannot_decide_continuation S) /\
  (verbatim_entry_support_kind .officialPeriodicTheoremOnT3 = .analyticDependent) /\
  (verbatim_theorem_support_kind .officialPeriodicTheoremOnT3 = .analyticDependent /\
   verbatim_theorem_support_kind .noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier = .analyticDependent) /\
  (verbatim_theorem_is_endpoint_downstream_simple .officialPeriodicTheoremOnT3 /\
   verbatim_theorem_is_endpoint_downstream_simple .noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PaperVerbatimStructuralEntriesCertifiedStatement
  · exact PaperVerbatimStructuralTheoremsCertifiedStatement
  · exact PaperVerbatimStructuralTitlesClosedSimpleStatement
  · exact PaperVerbatimNamedFailureBoundaryStatement
  · exact PaperVerbatimTheoremNamedFailureBoundaryStatement
  · exact PaperVerbatimNamedFailureTitleSimpleStatement
  · intro State Time Witness Candidate Quantity S
    exact PaperVortexStretchingCannotDecideContinuationStatement S
  · exact PaperVerbatimEndpointGapStatement
  · exact PaperVerbatimTheoremEndpointGapStatement
  · exact PaperVerbatimEndpointTitlesSimpleStatement

end MaleyLean
