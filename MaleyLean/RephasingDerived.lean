namespace MaleyLean

/--
Minimal derived witness layer for the rephasing paper.

`C` is the bookkeeping type and `W` is a canonical witness space. This layer
records the stronger derivation shape where operator-side and residual-phase
bookkeeping are both read off the same witness channel.
-/
structure RephasingWitnessData (C W : Type) where
  witness : C → W
  operatorWitness : C → W
  residualWitness : C → W

/--
If the operator-side and residual-side witness extractions both collapse to the
same canonical witness, then they agree pointwise.
-/
theorem operator_and_residual_phase_share_witness
  {C W : Type}
  (D : RephasingWitnessData C W)
  (h_operator :
    ∀ c : C, D.operatorWitness c = D.witness c)
  (h_residual :
    ∀ c : C, D.residualWitness c = D.witness c) :
  ∀ c : C, D.operatorWitness c = D.residualWitness c := by
  intro c
  calc
    D.operatorWitness c = D.witness c := h_operator c
    _ = D.residualWitness c := by
      symm
      exact h_residual c

/--
Derived no-split consequence at the witness layer.
-/
theorem no_rephasing_witness_split
  {C W : Type}
  (D : RephasingWitnessData C W)
  (h_operator :
    ∀ c : C, D.operatorWitness c = D.witness c)
  (h_residual :
    ∀ c : C, D.residualWitness c = D.witness c) :
  ¬ ∃ c : C, D.operatorWitness c ≠ D.residualWitness c := by
  intro hSplit
  rcases hSplit with ⟨c, hNe⟩
  exact hNe (operator_and_residual_phase_share_witness D h_operator h_residual c)

end MaleyLean
