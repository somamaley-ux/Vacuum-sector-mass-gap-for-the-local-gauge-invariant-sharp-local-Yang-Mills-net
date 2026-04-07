namespace MaleyLean

/--
Minimal derived witness layer for the FCNC paper.

`C` is the bookkeeping type and `W` is a canonical witness space. This layer
records the stronger derivation shape where alignment-side and FCNC-side
bookkeeping are both read off the same witness channel.
-/
structure FCNCWitnessData (C W : Type) where
  witness : C → W
  alignmentWitness : C → W
  fcncWitness : C → W

/--
If the alignment-side and FCNC-side witness extractions both collapse to the
same canonical witness, then they agree pointwise.
-/
theorem alignment_and_fcnc_share_witness
  {C W : Type}
  (D : FCNCWitnessData C W)
  (h_align :
    ∀ c : C, D.alignmentWitness c = D.witness c)
  (h_fcnc :
    ∀ c : C, D.fcncWitness c = D.witness c) :
  ∀ c : C, D.alignmentWitness c = D.fcncWitness c := by
  intro c
  calc
    D.alignmentWitness c = D.witness c := h_align c
    _ = D.fcncWitness c := by
      symm
      exact h_fcnc c

/--
Derived no-split consequence at the witness layer.
-/
theorem no_fcnc_witness_split
  {C W : Type}
  (D : FCNCWitnessData C W)
  (h_align :
    ∀ c : C, D.alignmentWitness c = D.witness c)
  (h_fcnc :
    ∀ c : C, D.fcncWitness c = D.witness c) :
  ¬ ∃ c : C, D.alignmentWitness c ≠ D.fcncWitness c := by
  intro hSplit
  rcases hSplit with ⟨c, hNe⟩
  exact hNe (alignment_and_fcnc_share_witness D h_align h_fcnc c)

end MaleyLean
