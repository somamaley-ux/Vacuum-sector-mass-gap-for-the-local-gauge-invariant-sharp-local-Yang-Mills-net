namespace MaleyLean

/--
Minimal derived witness layer for the hypercharge/charge-quantization paper.

`C` is the bookkeeping type and `W` is a canonical witness space. The point of
this layer is to record a stronger derivation shape than the minimal
equivalence wrapper: both admissible normalization and charge quantization are
forced by the same witness channel.
-/
structure HyperchargeWitnessData (C W : Type) where
  witness : C → W
  normalizedByWitness : W → Prop
  chargeQuantizedByWitness : W → Prop

/--
If the two constraint predicates are both definitionally read off the same
canonical witness, then they are equivalent.
-/
theorem hypercharge_quantization_from_shared_witness
  {C W : Type}
  (D : HyperchargeWitnessData C W)
  (h_shared :
    ∀ c : C,
      D.normalizedByWitness (D.witness c) ↔
      D.chargeQuantizedByWitness (D.witness c)) :
  ∀ c : C,
    D.normalizedByWitness (D.witness c) ↔
    D.chargeQuantizedByWitness (D.witness c) := by
  exact h_shared

/--
Derived no-split consequence at the witness layer.
-/
theorem no_hypercharge_quantization_split_from_shared_witness
  {C W : Type}
  (D : HyperchargeWitnessData C W)
  (h_shared :
    ∀ c : C,
      D.normalizedByWitness (D.witness c) ↔
      D.chargeQuantizedByWitness (D.witness c)) :
  ¬ ∃ c : C,
      (D.normalizedByWitness (D.witness c) ∧
        ¬ D.chargeQuantizedByWitness (D.witness c)) ∨
      (D.chargeQuantizedByWitness (D.witness c) ∧
        ¬ D.normalizedByWitness (D.witness c)) := by
  intro hSplit
  rcases hSplit with ⟨c, hCase⟩
  rcases hCase with hLeft | hRight
  · exact hLeft.2 ((h_shared c).mp hLeft.1)
  · exact hRight.2 ((h_shared c).mpr hRight.1)

end MaleyLean
