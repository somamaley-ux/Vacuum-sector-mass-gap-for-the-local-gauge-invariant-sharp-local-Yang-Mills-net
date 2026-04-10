namespace MaleyLean
namespace Papers
namespace MeasurementProblemReference
namespace Verbatim

/-- Verbatim manuscript title extracted from the supplied LaTeX source. -/
def manuscriptTitle : String :=
  "The Measurement Problem as a Problem of Reference"

/-- Verbatim manuscript subtitle extracted from the supplied LaTeX source. -/
def manuscriptSubtitle : String :=
  "Determinacy, Measurement Records, and Physically Non-Selective Theories"

/-- Main section spine extracted from `main.tex`. -/
inductive SectionTag where
  | introduction
  | targetClassAndClaim
  | semanticCore
  | branchingAndNonselection
  | measurementRecordsAndConfirmation
  | toyModelOfConfirmationalDivergence
  | memoryAnticipationAndAgency
  | selectorTaxonomy
  | objectionsAndReplies
  | nonclaimsAndScope
  | conclusion
  | appendixFormalRemarks
  | appendixRelationToLaterArchitecture
  | appendixHostileRefereeMaterials
deriving DecidableEq, Repr

def sectionTitle : SectionTag -> String
  | .introduction => "Introduction"
  | .targetClassAndClaim => "Target Class and Claim"
  | .semanticCore => "Semantic Core"
  | .branchingAndNonselection => "Branching and Non-Selection"
  | .measurementRecordsAndConfirmation => "Measurement Records and Confirmation"
  | .toyModelOfConfirmationalDivergence => "Toy Model of Confirmational Divergence"
  | .memoryAnticipationAndAgency => "Memory, Anticipation, and Agency"
  | .selectorTaxonomy => "Selector Taxonomy"
  | .objectionsAndReplies => "Objections and Replies"
  | .nonclaimsAndScope => "Non-Claims and Scope"
  | .conclusion => "Conclusion"
  | .appendixFormalRemarks => "Appendix A. Formal Remarks"
  | .appendixRelationToLaterArchitecture => "Appendix B. Relation to Later Architecture"
  | .appendixHostileRefereeMaterials => "Appendix C. Hostile Referee Materials"

/-- Main theorem-family register extracted from the manuscript. -/
inductive ResultTag where
  | compressedSubstrateNecessityBridge
  | measurementReferenceQuotientTheorem
  | globalEquivalenceCollapseTheorem
  | fixationCommutationNecessityForTheoryLevelConfirmation
  | everettianNonSelectionTheorem
  | decoherenceNonSelectionTheorem
  | everettianDownstreamTheorem
  | noAuxiliaryParameterizationOfTheoryLevelConfirmation
  | theoryLevelConfirmationCriterion
  | referenceStabilizationNecessity
  | hypothesisOrderReversalInTheToyModel
  | diachronicClosure
  | identityPreservingLineageTheorem
  | diachronicInheritanceTheorem
  | diachronicPracticeDependenceTheorem
  | structuralLocusTrichotomy
  | selectorExhaustionTheorem
  | interpretationTaxonomy
  | unresolvedAdmissibleDivergenceDestabilizesTheoryLevelScience
deriving DecidableEq, Repr

def resultTitle : ResultTag -> String
  | .compressedSubstrateNecessityBridge =>
      "Compressed substrate-necessity bridge"
  | .measurementReferenceQuotientTheorem =>
      "Measurement-reference quotient theorem"
  | .globalEquivalenceCollapseTheorem =>
      "Global equivalence-collapse theorem"
  | .fixationCommutationNecessityForTheoryLevelConfirmation =>
      "Fixation-commutation necessity for theory-level confirmation"
  | .everettianNonSelectionTheorem =>
      "Everettian non-selection theorem"
  | .decoherenceNonSelectionTheorem =>
      "Decoherence non-selection theorem"
  | .everettianDownstreamTheorem =>
      "Everettian downstream theorem"
  | .noAuxiliaryParameterizationOfTheoryLevelConfirmation =>
      "No auxiliary parameterization of theory-level confirmation"
  | .theoryLevelConfirmationCriterion =>
      "Theory-level confirmation criterion"
  | .referenceStabilizationNecessity =>
      "Reference-stabilization necessity"
  | .hypothesisOrderReversalInTheToyModel =>
      "Hypothesis-order reversal in the toy model"
  | .diachronicClosure =>
      "Diachronic closure"
  | .identityPreservingLineageTheorem =>
      "Identity-preserving lineage theorem"
  | .diachronicInheritanceTheorem =>
      "Diachronic inheritance theorem"
  | .diachronicPracticeDependenceTheorem =>
      "Diachronic practice dependence theorem"
  | .structuralLocusTrichotomy =>
      "Structural locus trichotomy"
  | .selectorExhaustionTheorem =>
      "Selector-exhaustion theorem"
  | .interpretationTaxonomy =>
      "Interpretation taxonomy"
  | .unresolvedAdmissibleDivergenceDestabilizesTheoryLevelScience =>
      "Unresolved admissible divergence destabilizes theory-level science"

/-- The four structural loci isolated in the taxonomy section. -/
def selectorLoci : List String :=
  [ "dynamic selection"
  , "ontic privileging"
  , "semantic restriction"
  , "discourse deflation"
  ]

theorem manuscriptHasRegisteredTitle :
    manuscriptTitle = "The Measurement Problem as a Problem of Reference" := by
  rfl

theorem manuscriptHasRegisteredSubtitle :
    manuscriptSubtitle =
      "Determinacy, Measurement Records, and Physically Non-Selective Theories" := by
  rfl

theorem manuscriptHasSelectorExhaustionEntry :
    resultTitle .selectorExhaustionTheorem = "Selector-exhaustion theorem" := by
  rfl

end Verbatim
end MeasurementProblemReference
end Papers
end MaleyLean
