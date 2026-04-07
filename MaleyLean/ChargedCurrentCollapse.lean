namespace MaleyLean

/--
Minimal domain skeleton for the charged-current support paper.

`UV` is the mediator bookkeeping skin, `Low` is the contact-interaction skin,
`Ext` is the enlarged scope skin, `W` is the restricted low-energy witness type
(for the `G_F`-style channel), and `V` is the additional enlarged-scope witness
type (for the `m_W`/higher-order channel).
-/
structure ChargedCurrentTransportData (UV Low Ext W V : Type) where
  transportRestricted : UV → Low
  transportExtended : UV → Ext
  uvRestrictedWitness : UV → W
  lowRestrictedWitness : Low → W
  uvExtendedWitness : UV → V
  extExtendedWitness : Ext → V

/--
A restricted-scope predicate is witness-complete when agreement of the single
restricted charged-current witness forces agreement on that predicate.
-/
def restricted_cc_witness_complete
  {UV Low Ext W V : Type}
  (D : ChargedCurrentTransportData UV Low Ext W V)
  (Relevant : (Low → Prop) → Prop) : Prop :=
  ∀ P : Low → Prop,
    Relevant P →
    ∀ b₁ b₂ : Low,
      D.lowRestrictedWitness b₁ = D.lowRestrictedWitness b₂ →
      (P b₁ ↔ P b₂)

/--
An independent restricted-scope charged-current degree would mean that some
relevant restricted-scope predicate distinguishes two UV configurations even
though transport assigns them the same low-energy witness.
-/
def independent_restricted_cc_degree
  {UV Low Ext W V : Type}
  (D : ChargedCurrentTransportData UV Low Ext W V)
  (Relevant : (Low → Prop) → Prop) : Prop :=
  ∃ P : Low → Prop,
    Relevant P ∧
    ∃ u₁ u₂ : UV,
      D.uvRestrictedWitness u₁ = D.uvRestrictedWitness u₂ ∧
      ¬ (P (D.transportRestricted u₁) ↔ P (D.transportRestricted u₂))

/--
Restricted-scope collapse:
if transport identifies UV bookkeeping with a single low-energy charged-current
witness, then that witness determines every relevant restricted-scope
predicate.
-/
theorem same_restricted_cc_witness_same_content
  {UV Low Ext W V : Type}
  (D : ChargedCurrentTransportData UV Low Ext W V)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowRestrictedWitness (D.transportRestricted u) = D.uvRestrictedWitness u)
  (h_complete :
    restricted_cc_witness_complete D Relevant)
  (P : Low → Prop)
  (hP : Relevant P)
  (u₁ u₂ : UV)
  (hEq : D.uvRestrictedWitness u₁ = D.uvRestrictedWitness u₂) :
  (P (D.transportRestricted u₁) ↔ P (D.transportRestricted u₂)) := by
  apply h_complete P hP
  calc
    D.lowRestrictedWitness (D.transportRestricted u₁)
        = D.uvRestrictedWitness u₁ := h_transport u₁
    _   = D.uvRestrictedWitness u₂ := hEq
    _   = D.lowRestrictedWitness (D.transportRestricted u₂) := by
          symm
          exact h_transport u₂

/--
Restricted-scope eliminative consequence:
once transport identifies the UV bookkeeping with a single low-energy witness,
there is no additional independent restricted-scope charged-current degree.
-/
theorem no_independent_restricted_cc_degree
  {UV Low Ext W V : Type}
  (D : ChargedCurrentTransportData UV Low Ext W V)
  (Relevant : (Low → Prop) → Prop)
  (h_transport :
    ∀ u : UV,
      D.lowRestrictedWitness (D.transportRestricted u) = D.uvRestrictedWitness u)
  (h_complete :
    restricted_cc_witness_complete D Relevant) :
  ¬ independent_restricted_cc_degree D Relevant := by
  intro hInd
  rcases hInd with ⟨P, hP, u₁, u₂, hEq, hSplit⟩
  exact
    hSplit
      (same_restricted_cc_witness_same_content
        D
        Relevant
        h_transport
        h_complete
        P
        hP
        u₁
        u₂
        hEq)

/--
Enlarged-scope witness expansion:
if the extended transport exposes an additional witness channel `V`, then that
channel is genuinely tracked in the enlarged scope.
-/
theorem extended_scope_tracks_additional_cc_witness
  {UV Low Ext W V : Type}
  (D : ChargedCurrentTransportData UV Low Ext W V)
  (h_transport_ext :
    ∀ u : UV,
      D.extExtendedWitness (D.transportExtended u) = D.uvExtendedWitness u)
  (u₁ u₂ : UV)
  (hEq :
    D.uvExtendedWitness u₁ = D.uvExtendedWitness u₂) :
  D.extExtendedWitness (D.transportExtended u₁) =
    D.extExtendedWitness (D.transportExtended u₂) := by
  calc
    D.extExtendedWitness (D.transportExtended u₁)
        = D.uvExtendedWitness u₁ := h_transport_ext u₁
    _   = D.uvExtendedWitness u₂ := hEq
    _   = D.extExtendedWitness (D.transportExtended u₂) := by
          symm
          exact h_transport_ext u₂

end MaleyLean
