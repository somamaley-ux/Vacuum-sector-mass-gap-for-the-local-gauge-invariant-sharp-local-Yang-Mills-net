import MaleyLean.ChargedCurrentCollapse

namespace MaleyLean

/--
Paper-facing support statement for
"Equivalence Completion and Forced Collapse of Charged Current".

This is the minimal faithful Lean surface for the current repo: it certifies the
restricted-scope single-witness collapse logic and the enlarged-scope witness
reappearance pattern without pretending that the full electroweak EFT matching
formulae have already been formalized here.
-/
theorem PaperChargedCurrentRestrictedCollapseStatement
  {UV Low Ext W V : Type}
  (D : ChargedCurrentTransportData UV Low Ext W V)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowRestrictedWitness (D.transportRestricted u) = D.uvRestrictedWitness u)
  (h_complete :
    restricted_cc_witness_complete D Relevant) :
  ∀ P : Low → Prop,
    Relevant P →
    ∀ u₁ u₂ : UV,
      D.uvRestrictedWitness u₁ = D.uvRestrictedWitness u₂ →
      (P (D.transportRestricted u₁) ↔ P (D.transportRestricted u₂)) := by
  intro P hP u₁ u₂ hEq
  exact
    same_restricted_cc_witness_same_content
      D
      Relevant
      h_transport
      h_complete
      P
      hP
      u₁
      u₂
      hEq

theorem PaperNoIndependentRestrictedChargedCurrentDegreeStatement
  {UV Low Ext W V : Type}
  (D : ChargedCurrentTransportData UV Low Ext W V)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowRestrictedWitness (D.transportRestricted u) = D.uvRestrictedWitness u)
  (h_complete :
    restricted_cc_witness_complete D Relevant) :
  ¬ independent_restricted_cc_degree D Relevant := by
  exact
    no_independent_restricted_cc_degree
      D
      Relevant
      h_transport
      h_complete

theorem PaperChargedCurrentExtendedScopeWitnessStatement
  {UV Low Ext W V : Type}
  (D : ChargedCurrentTransportData UV Low Ext W V)
  (h_transport_ext :
    ∀ u : UV,
      D.extExtendedWitness (D.transportExtended u) = D.uvExtendedWitness u) :
  ∀ u₁ u₂ : UV,
    D.uvExtendedWitness u₁ = D.uvExtendedWitness u₂ →
    D.extExtendedWitness (D.transportExtended u₁) =
      D.extExtendedWitness (D.transportExtended u₂) := by
  intro u₁ u₂ hEq
  exact
    extended_scope_tracks_additional_cc_witness
      D
      h_transport_ext
      u₁
      u₂
      hEq

end MaleyLean
