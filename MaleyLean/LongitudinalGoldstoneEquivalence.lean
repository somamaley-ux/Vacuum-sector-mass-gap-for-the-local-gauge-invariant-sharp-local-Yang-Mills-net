namespace MaleyLean

/--
Minimal domain skeleton for the longitudinal/Goldstone support paper.

`UV` is the higher-level field-level gauge bookkeeping skin, `Low` is the
admissible on-shell high-energy scattering skin, and `W` is the witness type
used to track the surviving longitudinal amplitude class.
-/
structure LongitudinalGoldstoneTransportData (UV Low W : Type) where
  transport : UV → Low
  uvWitness : UV → W
  lowWitness : Low → W

/--
A high-energy on-shell predicate is witness-complete when agreement of the
longitudinal amplitude witness forces agreement on that predicate.
-/
def longitudinal_witness_complete
  {UV Low W : Type}
  (D : LongitudinalGoldstoneTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop) : Prop :=
  ∀ P : Low → Prop,
    Relevant P →
    ∀ b₁ b₂ : Low,
      D.lowWitness b₁ = D.lowWitness b₂ →
      (P b₁ ↔ P b₂)

/--
An "independent longitudinal degree" would mean that some relevant on-shell
predicate distinguishes two UV configurations that transport to the same
surviving longitudinal witness.
-/
def independent_longitudinal_degree
  {UV Low W : Type}
  (D : LongitudinalGoldstoneTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop) : Prop :=
  ∃ P : Low → Prop,
    Relevant P ∧
    ∃ u₁ u₂ : UV,
      D.uvWitness u₁ = D.uvWitness u₂ ∧
      ¬ (P (D.transport u₁) ↔ P (D.transport u₂))

/--
If field-level bookkeeping transports to the same longitudinal witness, then
the same high-energy on-shell content follows for every relevant predicate.
-/
theorem same_longitudinal_witness_same_low_energy_content
  {UV Low W : Type}
  (D : LongitudinalGoldstoneTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowWitness (D.transport u) = D.uvWitness u)
  (h_complete :
    longitudinal_witness_complete D Relevant)
  (P : Low → Prop)
  (hP : Relevant P)
  (u₁ u₂ : UV)
  (hEq : D.uvWitness u₁ = D.uvWitness u₂) :
  (P (D.transport u₁) ↔ P (D.transport u₂)) := by
  apply h_complete P hP
  calc
    D.lowWitness (D.transport u₁)
        = D.uvWitness u₁ := h_transport u₁
    _   = D.uvWitness u₂ := hEq
    _   = D.lowWitness (D.transport u₂) := by
          symm
          exact h_transport u₂

/--
Paper-style eliminative consequence:
once transport identifies the field-level bookkeeping with a single surviving
longitudinal amplitude witness, there is no additional independent longitudinal
degree.
-/
theorem no_independent_longitudinal_degree
  {UV Low W : Type}
  (D : LongitudinalGoldstoneTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowWitness (D.transport u) = D.uvWitness u)
  (h_complete :
    longitudinal_witness_complete D Relevant) :
  ¬ independent_longitudinal_degree D Relevant := by
  intro hInd
  rcases hInd with ⟨P, hP, u₁, u₂, hEq, hSplit⟩
  exact
    hSplit
      (same_longitudinal_witness_same_low_energy_content
        D
        Relevant
        h_transport
        h_complete
        P
        hP
        u₁
        u₂
        hEq)

end MaleyLean
