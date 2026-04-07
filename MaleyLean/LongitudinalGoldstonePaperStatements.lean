import MaleyLean.LongitudinalGoldstoneEquivalence

namespace MaleyLean

/--
Paper-facing support statement for
"Equivalence Completion for Longitudinal Gauge Modes and Goldstone Degrees".

This is the minimal faithful Lean surface for the current repo: it certifies the
transport-collapse logic of the paper without pretending that the full
electroweak scattering amplitude machinery has already been formalized here.
-/
theorem PaperLongitudinalGoldstoneEquivalenceStatement
  {UV Low W : Type}
  (D : LongitudinalGoldstoneTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowWitness (D.transport u) = D.uvWitness u)
  (h_complete :
    longitudinal_witness_complete D Relevant) :
  ∀ P : Low → Prop,
    Relevant P →
    ∀ u₁ u₂ : UV,
      D.uvWitness u₁ = D.uvWitness u₂ →
      (P (D.transport u₁) ↔ P (D.transport u₂)) := by
  intro P hP u₁ u₂ hEq
  exact
    same_longitudinal_witness_same_low_energy_content
      D
      Relevant
      h_transport
      h_complete
      P
      hP
      u₁
      u₂
      hEq

theorem PaperNoIndependentLongitudinalDegreeStatement
  {UV Low W : Type}
  (D : LongitudinalGoldstoneTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowWitness (D.transport u) = D.uvWitness u)
  (h_complete :
    longitudinal_witness_complete D Relevant) :
  ¬ independent_longitudinal_degree D Relevant := by
  exact
    no_independent_longitudinal_degree
      D
      Relevant
      h_transport
      h_complete

end MaleyLean
