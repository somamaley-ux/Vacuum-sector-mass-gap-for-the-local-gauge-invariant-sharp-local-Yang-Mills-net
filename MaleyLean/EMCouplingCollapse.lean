namespace MaleyLean

/--
Minimal domain skeleton for the electroweak-to-electromagnetic support paper.

`UV` is the higher-level electroweak bookkeeping skin, `Low` is the admissible
electromagnetic bookkeeping skin, and `W` is the witness type used to track the
standing-relevant electromagnetic interaction strength.
-/
structure EMCouplingTransportData (UV Low W : Type) where
  transport : UV → Low
  uvWitness : UV → W
  lowWitness : Low → W

/--
A low-energy electromagnetic predicate is witness-complete when agreement of the
electromagnetic witness forces agreement on that predicate.
-/
def em_witness_complete
  {UV Low W : Type}
  (D : EMCouplingTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop) : Prop :=
  ∀ P : Low → Prop,
    Relevant P →
    ∀ b₁ b₂ : Low,
      D.lowWitness b₁ = D.lowWitness b₂ →
      (P b₁ ↔ P b₂)

/--
An "independent electromagnetic coupling degree" would mean that some relevant
electromagnetic predicate distinguishes two UV configurations that transport to
the same low-energy witness.
-/
def independent_em_coupling_degree
  {UV Low W : Type}
  (D : EMCouplingTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop) : Prop :=
  ∃ P : Low → Prop,
    Relevant P ∧
    ∃ u₁ u₂ : UV,
      D.uvWitness u₁ = D.uvWitness u₂ ∧
      ¬ (P (D.transport u₁) ↔ P (D.transport u₂))

/--
If electroweak bookkeeping transports to a single low-energy electromagnetic
witness, then the same witness forces the same low-energy electromagnetic
content for every relevant predicate.
-/
theorem same_em_witness_same_low_energy_content
  {UV Low W : Type}
  (D : EMCouplingTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowWitness (D.transport u) = D.uvWitness u)
  (h_complete :
    em_witness_complete D Relevant)
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
once transport identifies electroweak bookkeeping with a single electromagnetic
witness, there is no additional independent electromagnetic coupling degree.
-/
theorem no_independent_em_coupling_degree
  {UV Low W : Type}
  (D : EMCouplingTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowWitness (D.transport u) = D.uvWitness u)
  (h_complete :
    em_witness_complete D Relevant) :
  ¬ independent_em_coupling_degree D Relevant := by
  intro hInd
  rcases hInd with ⟨P, hP, u₁, u₂, hEq, hSplit⟩
  exact
    hSplit
      (same_em_witness_same_low_energy_content
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
