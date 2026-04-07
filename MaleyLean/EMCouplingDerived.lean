namespace MaleyLean

/--
Minimal derived witness layer for the electroweak/EM coupling paper.

`C` is the bookkeeping type and `W` is a canonical witness space. This layer
records a stronger derivation shape than the first-pass transport wrapper:
electroweak-side and electromagnetic-side coupling bookkeeping are both read
off the same witness channel.
-/
structure EMCouplingWitnessData (C W : Type) where
  witness : C → W
  ewWitness : C → W
  emWitness : C → W

/--
If the electroweak-side and electromagnetic-side witness extractions both
collapse to the same canonical witness, then they agree pointwise.
-/
theorem ew_and_em_share_witness
  {C W : Type}
  (D : EMCouplingWitnessData C W)
  (h_ew :
    ∀ c : C, D.ewWitness c = D.witness c)
  (h_em :
    ∀ c : C, D.emWitness c = D.witness c) :
  ∀ c : C, D.ewWitness c = D.emWitness c := by
  intro c
  calc
    D.ewWitness c = D.witness c := h_ew c
    _ = D.emWitness c := by
      symm
      exact h_em c

/--
Derived no-split consequence at the witness layer.
-/
theorem no_ew_em_witness_split
  {C W : Type}
  (D : EMCouplingWitnessData C W)
  (h_ew :
    ∀ c : C, D.ewWitness c = D.witness c)
  (h_em :
    ∀ c : C, D.emWitness c = D.witness c) :
  ¬ ∃ c : C, D.ewWitness c ≠ D.emWitness c := by
  intro hSplit
  rcases hSplit with ⟨c, hNe⟩
  exact hNe (ew_and_em_share_witness D h_ew h_em c)

end MaleyLean
