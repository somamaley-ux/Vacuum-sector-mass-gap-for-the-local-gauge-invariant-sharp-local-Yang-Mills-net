namespace MaleyLean

/--
Minimal domain skeleton for the neutrino-mixing support paper.

`UV` is the higher-level flavor/mass bookkeeping skin, `Low` is the admissible
oscillation-observable bookkeeping skin, `M` is the type of mass-difference
witness data, and `R` is the type of rephasing-invariant mixing witness data.
-/
structure NeutrinoMixingTransportData (UV Low M R : Type) where
  transport : UV → Low
  uvMassWitness : UV → M
  uvMixWitness : UV → R
  lowMassWitness : Low → M
  lowMixWitness : Low → R

/--
A low-energy oscillation predicate is witness-complete when agreement of both
the mass-difference witness and the rephasing-invariant mixing witness forces
agreement on that predicate.
-/
def oscillation_witness_complete
  {UV Low M R : Type}
  (D : NeutrinoMixingTransportData UV Low M R)
  (Relevant : (Low → Prop) → Prop) : Prop :=
  ∀ P : Low → Prop,
    Relevant P →
    ∀ b₁ b₂ : Low,
      D.lowMassWitness b₁ = D.lowMassWitness b₂ →
      D.lowMixWitness b₁ = D.lowMixWitness b₂ →
      (P b₁ ↔ P b₂)

/--
An "independent oscillation degree" would mean that some relevant oscillation
predicate distinguishes two UV configurations that agree on both surviving
witness channels after transport.
-/
def independent_oscillation_degree
  {UV Low M R : Type}
  (D : NeutrinoMixingTransportData UV Low M R)
  (Relevant : (Low → Prop) → Prop) : Prop :=
  ∃ P : Low → Prop,
    Relevant P ∧
    ∃ u₁ u₂ : UV,
      D.uvMassWitness u₁ = D.uvMassWitness u₂ ∧
      D.uvMixWitness u₁ = D.uvMixWitness u₂ ∧
      ¬ (P (D.transport u₁) ↔ P (D.transport u₂))

/--
If flavor/mass bookkeeping transports to the same mass-difference witness and
the same rephasing-invariant mixing witness, then the same oscillation content
follows for every relevant low-energy predicate.
-/
theorem same_oscillation_witnesses_same_low_energy_content
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
    oscillation_witness_complete D Relevant)
  (P : Low → Prop)
  (hP : Relevant P)
  (u₁ u₂ : UV)
  (hMass : D.uvMassWitness u₁ = D.uvMassWitness u₂)
  (hMix : D.uvMixWitness u₁ = D.uvMixWitness u₂) :
  (P (D.transport u₁) ↔ P (D.transport u₂)) := by
  apply h_complete P hP
  · calc
      D.lowMassWitness (D.transport u₁)
          = D.uvMassWitness u₁ := h_transport_mass u₁
      _   = D.uvMassWitness u₂ := hMass
      _   = D.lowMassWitness (D.transport u₂) := by
            symm
            exact h_transport_mass u₂
  · calc
      D.lowMixWitness (D.transport u₁)
          = D.uvMixWitness u₁ := h_transport_mix u₁
      _   = D.uvMixWitness u₂ := hMix
      _   = D.lowMixWitness (D.transport u₂) := by
            symm
            exact h_transport_mix u₂

/--
Paper-style eliminative consequence:
once transport identifies the UV bookkeeping with the two surviving oscillation
witness channels, there is no additional independent oscillation degree.
-/
theorem no_independent_oscillation_degree
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
  intro hInd
  rcases hInd with ⟨P, hP, u₁, u₂, hMass, hMix, hSplit⟩
  exact
    hSplit
      (same_oscillation_witnesses_same_low_energy_content
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
        hMix)

end MaleyLean
