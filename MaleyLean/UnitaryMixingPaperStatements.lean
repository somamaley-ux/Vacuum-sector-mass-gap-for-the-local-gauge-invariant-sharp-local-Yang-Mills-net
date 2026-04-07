import MaleyLean.UnitaryMixingSaturation

namespace MaleyLean

/--
Paper-facing support statement for
"Unitary Mixing Saturation under Admissible Transport".

This is the minimal faithful Lean surface for the current repo: it certifies the
saturation logic and the no-residual-mixing consequence without pretending that
the full operator-diagonalization algebra has already been formalized here.
-/
theorem PaperUnitaryMixingSaturationStatement
  {C : Type}
  (D : UnitaryMixingData C)
  (h_saturated :
    ∀ c : C, D.residualMixing c → D.operatorStructured c) :
  ∀ c : C, D.residualMixing c → D.operatorStructured c := by
  exact
    unitary_mixing_saturated_by_operator_structure
      D
      h_saturated

theorem PaperNoResidualUnitaryMixingStatement
  {C : Type}
  (D : UnitaryMixingData C)
  (h_saturated :
    ∀ c : C, D.residualMixing c → D.operatorStructured c) :
  ¬ residual_unitary_mixing_split D := by
  exact
    no_residual_unitary_mixing_split
      D
      h_saturated

end MaleyLean
