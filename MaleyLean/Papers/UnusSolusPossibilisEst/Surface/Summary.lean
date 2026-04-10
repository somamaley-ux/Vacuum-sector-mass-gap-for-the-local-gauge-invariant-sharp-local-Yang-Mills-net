import MaleyLean.Papers.UnusSolusPossibilisEst.Verbatim.TheoremRegister
import MaleyLean.Papers.UnusSolusPossibilisEst.ManuscriptTheorems

namespace MaleyLean
namespace Papers
namespace UnusSolusPossibilisEst
namespace Surface

/-- Summary theorem exposing the current manuscript-facing apex surface. -/
theorem SummaryStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_gate : GatePredicateExists S)
    (h_binary : BinaryStanding S)
    (h_param : NoAdmissibilityRelevantParameterization S)
    (h_unique_gate : UniqueGateClassification S)
    (h_no_repairs : NoRepairsForEvaluatedActs S)
    (h_no_generators : NoGenerators S)
    (h_no_carriers : NoPrimitiveCarriers S)
    (h_scope : NoIllicitScopeTransport S)
    (h_transfer : TransferWithoutStanding S)
    (h_fixation : ReferenceFixationNecessary S)
    (h_discrete : DiscreteMultiplicityElimination S)
    (h_unique : UniqueAdmissibleInterior S) :
    Verbatim.resultTitle Verbatim.ResultTag.apexStandaloneClosureTheorem =
      "Apex Standalone Closure Theorem" /\
    ApexStandaloneClosure S := by
  refine And.intro Verbatim.manuscriptHasApexClosureEntry ?_
  exact
    PaperApexStandaloneClosureStatement
      S h_gate h_binary h_param h_unique_gate h_no_repairs h_no_generators
      h_no_carriers h_scope h_transfer h_fixation h_discrete h_unique

end Surface
end UnusSolusPossibilisEst
end Papers
end MaleyLean
