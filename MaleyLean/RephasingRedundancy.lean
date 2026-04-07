namespace MaleyLean

/--
Minimal domain skeleton for the support paper
"Rephasing Redundancy Exhaustion under Admissible Transport".

`C` is the bookkeeping type for the fixed fermion content and admissible Yukawa
operator set. The predicates represent:
- phase data already encoded by admissible operator structure
- residual allegedly independent rephasing freedom
-/
structure RephasingData (C : Type) where
  operatorPhaseStructured : C → Prop
  residualPhase : C → Prop

/--
An apparent residual phase freedom would mean that some bookkeeping choice
carries rephasing data beyond admissible operator structure.
-/
def residual_rephasing_split
  {C : Type}
  (D : RephasingData C) : Prop :=
  ∃ c : C,
    D.residualPhase c ∧ ¬ D.operatorPhaseStructured c

/--
Core eliminative theorem: if every admissible residual phase datum is already
forced back into operator structure, then no independent physical phase survives
across skins.
-/
theorem rephasing_redundant_by_operator_structure
  {C : Type}
  (D : RephasingData C)
  (h_redundant :
    ∀ c : C, D.residualPhase c → D.operatorPhaseStructured c) :
  ∀ c : C, D.residualPhase c → D.operatorPhaseStructured c := by
  exact h_redundant

/--
No-split consequence:
if all admissible residual phases are forced back into operator structure, then
there is no bookkeeping choice carrying an extra independent physical phase.
-/
theorem no_residual_rephasing_split
  {C : Type}
  (D : RephasingData C)
  (h_redundant :
    ∀ c : C, D.residualPhase c → D.operatorPhaseStructured c) :
  ¬ residual_rephasing_split D := by
  intro hSplit
  rcases hSplit with ⟨c, hResidual, hNotStructured⟩
  exact hNotStructured (h_redundant c hResidual)

end MaleyLean
