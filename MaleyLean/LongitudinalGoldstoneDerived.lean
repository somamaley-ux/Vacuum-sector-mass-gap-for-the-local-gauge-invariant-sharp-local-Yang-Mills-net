namespace MaleyLean

/--
Minimal derived witness layer for the longitudinal/Goldstone paper.

`C` is the bookkeeping type and `W` is a canonical witness space. This layer
records the stronger derivation shape where longitudinal and Goldstone-side
bookkeeping are both read off the same surviving witness channel.
-/
structure LongitudinalGoldstoneWitnessData (C W : Type) where
  witness : C → W
  longitudinalWitness : C → W
  goldstoneWitness : C → W

/--
If the longitudinal-side and Goldstone-side witness extractions both collapse to
the same canonical witness, then they agree pointwise.
-/
theorem longitudinal_and_goldstone_share_witness
  {C W : Type}
  (D : LongitudinalGoldstoneWitnessData C W)
  (h_longitudinal :
    ∀ c : C, D.longitudinalWitness c = D.witness c)
  (h_goldstone :
    ∀ c : C, D.goldstoneWitness c = D.witness c) :
  ∀ c : C, D.longitudinalWitness c = D.goldstoneWitness c := by
  intro c
  calc
    D.longitudinalWitness c = D.witness c := h_longitudinal c
    _ = D.goldstoneWitness c := by
      symm
      exact h_goldstone c

/--
Derived no-split consequence at the witness layer.
-/
theorem no_longitudinal_goldstone_witness_split
  {C W : Type}
  (D : LongitudinalGoldstoneWitnessData C W)
  (h_longitudinal :
    ∀ c : C, D.longitudinalWitness c = D.witness c)
  (h_goldstone :
    ∀ c : C, D.goldstoneWitness c = D.witness c) :
  ¬ ∃ c : C, D.longitudinalWitness c ≠ D.goldstoneWitness c := by
  intro hSplit
  rcases hSplit with ⟨c, hNe⟩
  exact hNe (longitudinal_and_goldstone_share_witness D h_longitudinal h_goldstone c)

end MaleyLean
