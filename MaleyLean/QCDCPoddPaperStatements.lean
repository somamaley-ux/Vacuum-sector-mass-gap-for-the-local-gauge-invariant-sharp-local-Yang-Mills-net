import MaleyLean.QCDCPoddCollapse

namespace MaleyLean

/--
Paper-facing support statement for
"Equivalence Completion in the QCD CP-Odd Sector".

This is the minimal faithful Lean surface for the current repo: it certifies the
single-witness collapse logic of the paper without pretending that the full
Fujikawa/Jacobian arithmetic or the explicit formula `bar theta = theta + arg det M`
has already been formalized here.
-/
theorem PaperQCDBarThetaInvariantStatement
  {Γ : Type}
  [AddGroup Γ]
  (delta theta argdetM : Γ) :
  barTheta
      (thetaAfterRephasing delta theta)
      (argdetAfterRephasing delta argdetM)
    =
      barTheta theta argdetM := by
  exact
    barTheta_invariant_under_opposite_rephasing_shifts
      delta
      theta
      argdetM

theorem PaperQCDCPoddCollapseStatement
  {UV W : Type}
  (D : QCDCPoddData UV W)
  (P : UV → Prop)
  (h_complete :
    ∀ u₁ u₂ : UV,
      D.cpOddWitness u₁ = D.cpOddWitness u₂ →
      (P u₁ ↔ P u₂)) :
  ∀ u₁ u₂ : UV,
    D.cpOddWitness u₁ = D.cpOddWitness u₂ →
    (P u₁ ↔ P u₂) := by
  exact
    cpodd_collapse_to_single_witness
      D
      P
      h_complete

theorem PaperNoQCDCPoddObservableSplitStatement
  {UV W : Type}
  (D : QCDCPoddData UV W)
  (Observable : UV → Prop)
  (h_complete :
    ∀ u₁ u₂ : UV,
      D.cpOddWitness u₁ = D.cpOddWitness u₂ →
      (Observable u₁ ↔ Observable u₂)) :
  ∀ u₁ u₂ : UV,
    D.cpOddWitness u₁ = D.cpOddWitness u₂ →
    (Observable u₁ ↔ Observable u₂) := by
  exact
    no_cpodd_observable_split
      D
      Observable
      h_complete

end MaleyLean
