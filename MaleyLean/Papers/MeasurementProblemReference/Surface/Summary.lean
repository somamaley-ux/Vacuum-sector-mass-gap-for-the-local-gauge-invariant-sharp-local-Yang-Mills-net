import MaleyLean.Papers.MeasurementProblemReference.PaperStatements

namespace MaleyLean
namespace Papers
namespace MeasurementProblemReference
namespace Surface

theorem SummaryStatement :
    Verbatim.manuscriptTitle = "The Measurement Problem as a Problem of Reference" /\
    Verbatim.resultTitle Verbatim.ResultTag.measurementReferenceQuotientTheorem =
      "Measurement-reference quotient theorem" /\
    Verbatim.resultTitle Verbatim.ResultTag.everettianNonSelectionTheorem =
      "Everettian non-selection theorem" /\
    Verbatim.resultTitle Verbatim.ResultTag.selectorExhaustionTheorem =
      "Selector-exhaustion theorem" := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

theorem CurrentDerivedSummaryStatement
    {Assignment Report Assertion Target : Type}
    (ctx : ConfirmationDerivedContext Assignment Report Assertion Target)
    (sem : SemanticDerivedContext Report)
    (stateCarries :
      EverettToyState ->
      EverettAuxiliarySpec EverettToyFactorization ->
      Prop)
    (h_not_reified : Not (selector_reified_as_state stateCarries)) :
    orbit_respects_invariants sem.A sem.B /\
    invariants_exhaust_orbits sem.A sem.B /\
    (exists rho : EverettToyState,
      exists sigma tau : EverettAuxiliarySpec EverettToyFactorization,
        everettToyBranchingData.extract rho sigma ≠
          everettToyBranchingData.extract rho tau) /\
    Not (decoherence_record_state_determined everettToyDecoherenceData) /\
    theory_level_confirmation_possible ctx.confirmationPractice /\
    reference_fixation ctx.confirmationPractice ctx.referenceMap := by
  have hCore :=
    PaperMeasurementProblemReferenceCurrentDerivedCoreStatement
      ctx
      sem
      stateCarries
      h_not_reified
  rcases hCore with
    ⟨hQuot, hCollapse, _hFixComm, hEverett, hDecoherence, _hDownstream, hTheory, hFix⟩
  exact And.intro hQuot <|
    And.intro hCollapse <|
      And.intro hEverett <|
        And.intro hDecoherence <|
          And.intro hTheory hFix

theorem DiachronicCurrentSummaryStatement
    {Agent Time Record Assignment Report Assertion Target : Type}
    (ctx : DiachronicDerivedContext Agent Time Record Assignment Report Assertion Target) :
    SharedQuotientFactorization ctx.diachronic /\
    MemoryDependsOnReference ctx.diachronic /\
    AnticipationDependsOnSuccessorTyping ctx.diachronic /\
    AgencyNeedsTypedFutureRecords ctx.diachronic /\
    theory_level_confirmation_possible ctx.confirmation.confirmationPractice := by
  exact PaperMeasurementProblemReferenceDiachronicCurrentStatement ctx

theorem SelectorCurrentSummaryStatement
    (ctx : SelectorDerivedContext) :
    BoundarySelectorForbidden ctx.package /\
    QuotientRefinementForcesScopeChange ctx.package /\
    RepresentationRestrictionImpliesSemanticOrDeflation ctx.package /\
    (ctx.package.dynamicSelection \/
      ctx.package.onticPrivileging \/
      ctx.package.semanticRestriction \/
      ctx.package.discourseDeflation) := by
  exact PaperMeasurementProblemReferenceSelectorCurrentStatement ctx

end Surface
end MeasurementProblemReference
end Papers
end MaleyLean
