namespace MaleyLean

/--
Minimal derived witness layer for the anomaly/Yukawa paper.

`C` is the bookkeeping type and `W` is a canonical witness space. This layer
records the stronger derivation shape where anomaly-side and Yukawa-side
bookkeeping are both read off the same admissibility witness channel.
-/
structure AnomalyYukawaWitnessData (C W : Type) where
  witness : C → W
  anomalyWitness : C → W
  yukawaWitness : C → W

/--
If the anomaly-side and Yukawa-side witness extractions both collapse to the
same canonical witness, then they agree pointwise.
-/
theorem anomaly_and_yukawa_share_witness
  {C W : Type}
  (D : AnomalyYukawaWitnessData C W)
  (h_anomaly :
    ∀ c : C, D.anomalyWitness c = D.witness c)
  (h_yukawa :
    ∀ c : C, D.yukawaWitness c = D.witness c) :
  ∀ c : C, D.anomalyWitness c = D.yukawaWitness c := by
  intro c
  calc
    D.anomalyWitness c = D.witness c := h_anomaly c
    _ = D.yukawaWitness c := by
      symm
      exact h_yukawa c

/--
Derived no-split consequence at the witness layer.
-/
theorem no_anomaly_yukawa_witness_split
  {C W : Type}
  (D : AnomalyYukawaWitnessData C W)
  (h_anomaly :
    ∀ c : C, D.anomalyWitness c = D.witness c)
  (h_yukawa :
    ∀ c : C, D.yukawaWitness c = D.witness c) :
  ¬ ∃ c : C, D.anomalyWitness c ≠ D.yukawaWitness c := by
  intro hSplit
  rcases hSplit with ⟨c, hNe⟩
  exact hNe (anomaly_and_yukawa_share_witness D h_anomaly h_yukawa c)

end MaleyLean
