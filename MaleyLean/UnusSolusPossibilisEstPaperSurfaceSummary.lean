import MaleyLean.Papers.UnusSolusPossibilisEst.Surface.Summary

namespace MaleyLean

/--
Top-level export wrapper for the manuscript-facing `Unus Solus Possibilis Est`
paper surface.
-/
theorem UnusSolusPossibilisEstPaperSurfaceSummaryStatement
    {Act Domain : Type}
    (S : Papers.UnusSolusPossibilisEst.ApexClosureSystem Act Domain)
    (h_gate : Papers.UnusSolusPossibilisEst.GatePredicateExists S)
    (h_binary : Papers.UnusSolusPossibilisEst.BinaryStanding S)
    (h_param : Papers.UnusSolusPossibilisEst.NoAdmissibilityRelevantParameterization S)
    (h_unique_gate : Papers.UnusSolusPossibilisEst.UniqueGateClassification S)
    (h_no_repairs : Papers.UnusSolusPossibilisEst.NoRepairsForEvaluatedActs S)
    (h_no_generators : Papers.UnusSolusPossibilisEst.NoGenerators S)
    (h_no_carriers : Papers.UnusSolusPossibilisEst.NoPrimitiveCarriers S)
    (h_scope : Papers.UnusSolusPossibilisEst.NoIllicitScopeTransport S)
    (h_transfer : Papers.UnusSolusPossibilisEst.TransferWithoutStanding S)
    (h_fixation : Papers.UnusSolusPossibilisEst.ReferenceFixationNecessary S)
    (h_discrete : Papers.UnusSolusPossibilisEst.DiscreteMultiplicityElimination S)
    (h_unique : Papers.UnusSolusPossibilisEst.UniqueAdmissibleInterior S) :
    Papers.UnusSolusPossibilisEst.Verbatim.resultTitle
        Papers.UnusSolusPossibilisEst.Verbatim.ResultTag.apexStandaloneClosureTheorem =
      "Apex Standalone Closure Theorem" /\
    Papers.UnusSolusPossibilisEst.ApexStandaloneClosure S := by
  exact
    Papers.UnusSolusPossibilisEst.Surface.SummaryStatement
      S h_gate h_binary h_param h_unique_gate h_no_repairs h_no_generators
      h_no_carriers h_scope h_transfer h_fixation h_discrete h_unique

end MaleyLean
