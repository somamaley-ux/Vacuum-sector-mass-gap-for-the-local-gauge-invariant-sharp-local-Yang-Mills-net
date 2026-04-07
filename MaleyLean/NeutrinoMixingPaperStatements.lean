import MaleyLean.NeutrinoMixingInvariants

namespace MaleyLean

/--
Paper-facing support statement for
"Equivalence Completion for Neutrino Mixing and Oscillation Invariants".

This is the minimal faithful Lean surface for the current repo: it certifies the
transport-collapse logic of the paper without pretending that the full
oscillation probability formula or explicit PMNS parameter arithmetic has
already been formalized here.
-/
theorem PaperNeutrinoMixingInvariantSurfaceStatement
  {UV Low M R : Type}
  (D : NeutrinoMixingTransportData UV Low M R)
  (Relevant : (Low → Prop) → Prop)
  (h_transport_mass :
    ∀ u : UV,
      D.lowMassWitness (D.transport u) = D.uvMassWitness u)
  (h_transport_mix :
    ∀ u : UV,
      D.lowMixWitness (D.transport u) = D.uvMixWitness u)
  (h_complete :
    oscillation_witness_complete D Relevant) :
  ∀ P : Low → Prop,
    Relevant P →
    ∀ u₁ u₂ : UV,
      D.uvMassWitness u₁ = D.uvMassWitness u₂ →
      D.uvMixWitness u₁ = D.uvMixWitness u₂ →
      (P (D.transport u₁) ↔ P (D.transport u₂)) := by
  intro P hP u₁ u₂ hMass hMix
  exact
    same_oscillation_witnesses_same_low_energy_content
      D
      Relevant
      h_transport_mass
      h_transport_mix
      h_complete
      P
      hP
      u₁
      u₂
      hMass
      hMix

theorem PaperNoIndependentOscillationDegreeStatement
  {UV Low M R : Type}
  (D : NeutrinoMixingTransportData UV Low M R)
  (Relevant : (Low → Prop) → Prop)
  (h_transport_mass :
    ∀ u : UV,
      D.lowMassWitness (D.transport u) = D.uvMassWitness u)
  (h_transport_mix :
    ∀ u : UV,
      D.lowMixWitness (D.transport u) = D.uvMixWitness u)
  (h_complete :
    oscillation_witness_complete D Relevant) :
  ¬ independent_oscillation_degree D Relevant := by
  exact
    no_independent_oscillation_degree
      D
      Relevant
      h_transport_mass
      h_transport_mix
      h_complete

end MaleyLean
