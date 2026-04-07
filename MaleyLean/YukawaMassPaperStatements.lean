import MaleyLean.YukawaMassEquivalence

namespace MaleyLean

/--
Paper-facing support statement for
"Equivalence Completion Between Yukawa and Mass Bookkeeping".

This is a minimal faithful Lean surface for the current repo: it certifies the
transport-collapse logic of the paper without pretending that the full Standard-
Model field content or the explicit arithmetic formula `m_f = y_f v / sqrt(2)`
has already been formalized here.
-/
theorem PaperFermionYukawaMassEquivalenceStatement
  {UV Low W : Type}
  (D : YukawaMassTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowWitness (D.transport u) = D.uvWitness u)
  (h_complete :
    witness_complete D Relevant) :
  ∀ P : Low → Prop,
    Relevant P →
    ∀ u₁ u₂ : UV,
      D.uvWitness u₁ = D.uvWitness u₂ →
      (P (D.transport u₁) ↔ P (D.transport u₂)) := by
  intro P hP u₁ u₂ hEq
  exact
    same_witness_same_low_energy_content
      D
      Relevant
      h_transport
      h_complete
      P
      hP
      u₁
      u₂
      hEq

theorem PaperNoIndependentYukawaDegreeStatement
  {UV Low W : Type}
  (D : YukawaMassTransportData UV Low W)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowWitness (D.transport u) = D.uvWitness u)
  (h_complete :
    witness_complete D Relevant) :
  ¬ independent_low_energy_yukawa_degree D Relevant := by
  exact
    no_independent_low_energy_yukawa_degree
      D
      Relevant
      h_transport
      h_complete

end MaleyLean
