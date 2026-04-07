import MaleyLean.UnitaryMixingPaperStatements
import MaleyLean.UnitaryMixingDerived

namespace MaleyLean

/--
Derived paper-facing shared-witness statement for the unitary-mixing paper.

This strengthens the first-pass support surface by recording that operator-side
and residual-side unitary-mixing bookkeeping collapse to a common canonical
witness channel.
-/
theorem PaperUnitaryMixingSharedWitnessStatement
  {C W : Type}
  (D : UnitaryMixingWitnessData C W)
  (h_operator :
    ∀ c : C, D.operatorWitness c = D.witness c)
  (h_residual :
    ∀ c : C, D.residualWitness c = D.witness c) :
  ∀ c : C, D.operatorWitness c = D.residualWitness c := by
  exact
    operator_and_residual_mixing_share_witness
      D
      h_operator
      h_residual

theorem PaperNoUnitaryMixingWitnessSplitStatement
  {C W : Type}
  (D : UnitaryMixingWitnessData C W)
  (h_operator :
    ∀ c : C, D.operatorWitness c = D.witness c)
  (h_residual :
    ∀ c : C, D.residualWitness c = D.witness c) :
  ¬ ∃ c : C, D.operatorWitness c ≠ D.residualWitness c := by
  exact
    no_unitary_mixing_witness_split
      D
      h_operator
      h_residual

end MaleyLean
