namespace MaleyLean

/--
Minimal domain skeleton for the support paper
"Unitary Mixing Saturation under Admissible Transport".

`C` is the bookkeeping type for the fixed chiral load. The predicates represent:
- admissible operator-structured mixing data
- residual allegedly independent unitary mixing freedom
-/
structure UnitaryMixingData (C : Type) where
  operatorStructured : C → Prop
  residualMixing : C → Prop

/--
An apparent residual mixing freedom would mean that some bookkeeping choice
carries unitary mixing data beyond admissible operator structure.
-/
def residual_unitary_mixing_split
  {C : Type}
  (D : UnitaryMixingData C) : Prop :=
  ∃ c : C,
    D.residualMixing c ∧ ¬ D.operatorStructured c

/--
Core eliminative theorem: if every admissible unitary mixing datum is already
saturated by operator structure, then residual independent unitary mixing does
not survive across skins.
-/
theorem unitary_mixing_saturated_by_operator_structure
  {C : Type}
  (D : UnitaryMixingData C)
  (h_saturated :
    ∀ c : C, D.residualMixing c → D.operatorStructured c) :
  ∀ c : C, D.residualMixing c → D.operatorStructured c := by
  exact h_saturated

/--
No-split consequence:
if all admissible residual mixing is forced back into operator structure, then
there is no bookkeeping choice carrying an extra independent unitary mixing
degree.
-/
theorem no_residual_unitary_mixing_split
  {C : Type}
  (D : UnitaryMixingData C)
  (h_saturated :
    ∀ c : C, D.residualMixing c → D.operatorStructured c) :
  ¬ residual_unitary_mixing_split D := by
  intro hSplit
  rcases hSplit with ⟨c, hResidual, hNotStructured⟩
  exact hNotStructured (h_saturated c hResidual)

end MaleyLean
