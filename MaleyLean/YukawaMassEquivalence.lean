namespace MaleyLean

/--
Minimal domain skeleton for the Yukawa/mass support paper.

`UV` is the higher-level Higgs/Yukawa bookkeeping skin, `Low` is the admissible
low-energy mass bookkeeping skin, and `W` is the witness type used to track the
standing-relevant fermion-sector content for a fixed species.
-/
structure YukawaMassTransportData (UV Low W : Type) where
  transport : UV → Low
  uvWitness : UV → W
  lowWitness : Low → W

/--
A candidate low-energy predicate is relevant when the user of the theorem wants
to treat it as standing-relevant low-energy content for the fixed species/scope.
The theorem below does not decide relevance; it only shows that once all relevant
predicates are witness-complete, no extra independent low-energy Yukawa degree
remains beyond that witness.
-/
def witness_complete
  {UV Low W : Type}
  (D : YukawaMassTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop) : Prop :=
  ∀ P : Low → Prop,
    Relevant P →
    ∀ b₁ b₂ : Low,
      D.lowWitness b₁ = D.lowWitness b₂ →
      (P b₁ ↔ P b₂)

/--
An "independent low-energy Yukawa degree" would mean that some relevant
low-energy predicate can distinguish two UV configurations even though transport
assigns them the same witness in the low-energy skin.
-/
def independent_low_energy_yukawa_degree
  {UV Low W : Type}
  (D : YukawaMassTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop) : Prop :=
  ∃ P : Low → Prop,
    Relevant P ∧
    ∃ u₁ u₂ : UV,
      D.uvWitness u₁ = D.uvWitness u₂ ∧
      ¬ (P (D.transport u₁) ↔ P (D.transport u₂))

/--
Cross-skin transport collapses the UV bookkeeping to the low-energy witness:
if the transported low-energy witness agrees with the UV witness and all
standing-relevant low-energy predicates are witness-complete, then two UV states
with the same witness are indistinguishable by every relevant low-energy
predicate.
-/
theorem same_witness_same_low_energy_content
  {UV Low W : Type}
  (D : YukawaMassTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowWitness (D.transport u) = D.uvWitness u)
  (h_complete :
    witness_complete D Relevant)
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
once transport identifies the UV bookkeeping with a single low-energy witness,
there is no additional independent low-energy Yukawa degree.
-/
theorem no_independent_low_energy_yukawa_degree
  {UV Low W : Type}
  (D : YukawaMassTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowWitness (D.transport u) = D.uvWitness u)
  (h_complete :
    witness_complete D Relevant) :
  ¬ independent_low_energy_yukawa_degree D Relevant := by
  intro hInd
  rcases hInd with ⟨P, hP, u₁, u₂, hEq, hSplit⟩
  exact
    hSplit
      (same_witness_same_low_energy_content
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
