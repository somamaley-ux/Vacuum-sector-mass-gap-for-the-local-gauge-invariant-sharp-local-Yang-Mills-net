import MaleyLean.QCDCPoddPaperStatements
import MaleyLean.QCDCPoddDerived

namespace MaleyLean

theorem PaperQCDBarThetaInvariantDerivedStatement
  {G : Type}
  [AddGroup G]
  (delta theta argdetM : G) :
  barThetaDerived
      (thetaAfterRephasingDerived delta theta)
      (argdetAfterRephasingDerived delta argdetM)
    =
      barThetaDerived theta argdetM := by
  exact
    barThetaDerived_invariant_under_opposite_rephasing_shifts
      delta
      theta
      argdetM

end MaleyLean
