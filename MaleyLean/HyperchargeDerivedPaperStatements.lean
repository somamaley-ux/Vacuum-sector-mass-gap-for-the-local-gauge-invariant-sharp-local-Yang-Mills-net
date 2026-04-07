import MaleyLean.HyperchargePaperStatements
import MaleyLean.HyperchargeDerived

namespace MaleyLean

/--
Derived paper-facing witness-collapse statement for the hypercharge paper.

This strengthens the first-pass support surface by recording a shared-witness
derivation path rather than only the abstract mutual-implication layer.
-/
theorem PaperHyperchargeSharedWitnessStatement
  {C W : Type}
  (D : HyperchargeWitnessData C W)
  (h_shared :
    ∀ c : C,
      D.normalizedByWitness (D.witness c) ↔
      D.chargeQuantizedByWitness (D.witness c)) :
  ∀ c : C,
    D.normalizedByWitness (D.witness c) ↔
    D.chargeQuantizedByWitness (D.witness c) := by
  exact
    hypercharge_quantization_from_shared_witness
      D
      h_shared

theorem PaperNoHyperchargeSharedWitnessSplitStatement
  {C W : Type}
  (D : HyperchargeWitnessData C W)
  (h_shared :
    ∀ c : C,
      D.normalizedByWitness (D.witness c) ↔
      D.chargeQuantizedByWitness (D.witness c)) :
  ¬ ∃ c : C,
      (D.normalizedByWitness (D.witness c) ∧
        ¬ D.chargeQuantizedByWitness (D.witness c)) ∨
      (D.chargeQuantizedByWitness (D.witness c) ∧
        ¬ D.normalizedByWitness (D.witness c)) := by
  exact
    no_hypercharge_quantization_split_from_shared_witness
      D
      h_shared

end MaleyLean
