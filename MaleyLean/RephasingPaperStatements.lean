import MaleyLean.RephasingRedundancy

namespace MaleyLean

/--
Paper-facing support statement for
"Rephasing Redundancy Exhaustion under Admissible Transport".

This is the minimal faithful Lean surface for the current repo: it certifies the
redundancy logic and the no-residual-phase consequence without pretending that
the full field-redefinition algebra has already been formalized here.
-/
theorem PaperRephasingRedundancyStatement
  {C : Type}
  (D : RephasingData C)
  (h_redundant :
    ∀ c : C, D.residualPhase c → D.operatorPhaseStructured c) :
  ∀ c : C, D.residualPhase c → D.operatorPhaseStructured c := by
  exact
    rephasing_redundant_by_operator_structure
      D
      h_redundant

theorem PaperNoResidualRephasingStatement
  {C : Type}
  (D : RephasingData C)
  (h_redundant :
    ∀ c : C, D.residualPhase c → D.operatorPhaseStructured c) :
  ¬ residual_rephasing_split D := by
  exact
    no_residual_rephasing_split
      D
      h_redundant

end MaleyLean
