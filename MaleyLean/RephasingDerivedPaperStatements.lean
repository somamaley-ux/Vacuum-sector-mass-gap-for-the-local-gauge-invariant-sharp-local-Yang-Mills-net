import MaleyLean.RephasingPaperStatements
import MaleyLean.RephasingDerived

namespace MaleyLean

/--
Derived paper-facing shared-witness statement for the rephasing paper.

This strengthens the first-pass support surface by recording that operator-side
and residual-phase bookkeeping collapse to a common canonical witness channel.
-/
theorem PaperRephasingSharedWitnessStatement
  {C W : Type}
  (D : RephasingWitnessData C W)
  (h_operator :
    ∀ c : C, D.operatorWitness c = D.witness c)
  (h_residual :
    ∀ c : C, D.residualWitness c = D.witness c) :
  ∀ c : C, D.operatorWitness c = D.residualWitness c := by
  exact
    operator_and_residual_phase_share_witness
      D
      h_operator
      h_residual

theorem PaperNoRephasingWitnessSplitStatement
  {C W : Type}
  (D : RephasingWitnessData C W)
  (h_operator :
    ∀ c : C, D.operatorWitness c = D.witness c)
  (h_residual :
    ∀ c : C, D.residualWitness c = D.witness c) :
  ¬ ∃ c : C, D.operatorWitness c ≠ D.residualWitness c := by
  exact
    no_rephasing_witness_split
      D
      h_operator
      h_residual

end MaleyLean
