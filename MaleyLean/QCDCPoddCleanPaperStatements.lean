import MaleyLean.QCDCPoddCoreClean

namespace MaleyLean

theorem PaperQCDBarThetaInvariantCleanStatement
  {G : Type}
  (ops : CPoddPhaseOpsClean G)
  (delta theta argdetM : G) :
  barThetaClean
      ops
      (thetaAfterRephasingClean ops delta theta)
      (argdetAfterRephasingClean ops delta argdetM)
    =
      barThetaClean ops theta argdetM := by
  exact
    barThetaClean_invariant_under_opposite_rephasing_shifts
      ops
      delta
      theta
      argdetM

theorem PaperQCDCPoddCollapseCleanStatement
  {UV W : Type}
  (D : QCDCPoddDataClean UV W)
  (P : UV → Prop)
  (h_complete :
    ∀ u₁ u₂ : UV,
      D.cpOddWitness u₁ = D.cpOddWitness u₂ →
      (P u₁ ↔ P u₂)) :
  ∀ u₁ u₂ : UV,
    D.cpOddWitness u₁ = D.cpOddWitness u₂ →
    (P u₁ ↔ P u₂) := by
  exact
    cpodd_collapse_to_single_witness_clean
      D
      P
      h_complete

theorem PaperNoQCDCPoddObservableSplitCleanStatement
  {UV W : Type}
  (D : QCDCPoddDataClean UV W)
  (Observable : UV → Prop)
  (h_complete :
    ∀ u₁ u₂ : UV,
      D.cpOddWitness u₁ = D.cpOddWitness u₂ →
      (Observable u₁ ↔ Observable u₂)) :
  ∀ u₁ u₂ : UV,
    D.cpOddWitness u₁ = D.cpOddWitness u₂ →
    (Observable u₁ ↔ Observable u₂) := by
  exact
    no_cpodd_observable_split_clean
      D
      Observable
      h_complete

end MaleyLean
