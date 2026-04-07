namespace MaleyLean

/--
Minimal derived witness layer for the Yukawa/mass paper.

`C` is the bookkeeping type and `W` is a canonical witness space. This layer
records a stronger derivation shape than the first-pass transport wrapper:
mass-side and Yukawa-side bookkeeping are both read off the same witness
channel.
-/
structure YukawaMassWitnessData (C W : Type) where
  witness : C → W
  massWitness : C → W
  yukawaWitness : C → W

/--
If the mass-side and Yukawa-side witness extractions both collapse to the same
canonical witness, then they agree pointwise.
-/
theorem mass_and_yukawa_share_witness
  {C W : Type}
  (D : YukawaMassWitnessData C W)
  (h_mass :
    ∀ c : C, D.massWitness c = D.witness c)
  (h_yukawa :
    ∀ c : C, D.yukawaWitness c = D.witness c) :
  ∀ c : C, D.massWitness c = D.yukawaWitness c := by
  intro c
  calc
    D.massWitness c = D.witness c := h_mass c
    _ = D.yukawaWitness c := by
      symm
      exact h_yukawa c

/--
Derived no-split consequence at the witness layer.
-/
theorem no_yukawa_mass_witness_split
  {C W : Type}
  (D : YukawaMassWitnessData C W)
  (h_mass :
    ∀ c : C, D.massWitness c = D.witness c)
  (h_yukawa :
    ∀ c : C, D.yukawaWitness c = D.witness c) :
  ¬ ∃ c : C, D.massWitness c ≠ D.yukawaWitness c := by
  intro hSplit
  rcases hSplit with ⟨c, hNe⟩
  exact hNe (mass_and_yukawa_share_witness D h_mass h_yukawa c)

end MaleyLean
