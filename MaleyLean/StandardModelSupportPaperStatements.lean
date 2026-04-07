import MaleyLean.YukawaMassPaperStatements
import MaleyLean.EMCouplingPaperStatements
import MaleyLean.AnomalyYukawaPaperStatements
import MaleyLean.EquivalenceExhaustionPaperStatements

namespace MaleyLean

/--
Aggregate paper-facing support surface currently formalized for the Standard-
Model manuscript's L1 support stack.

This bundles the support-paper layers that are presently represented in Lean:

- Paper 3: Yukawa/mass transport collapse
- Paper 4: electroweak/electromagnetic coupling collapse
- Paper 7: anomaly/Yukawa equivalence under minimal chiral load
- Paper 12: relative equivalence exhaustion / closure

It is intentionally partial: it does not claim that the full L1 support stack is
encoded, only that these four support layers are available as axiom-free Lean
surfaces.
-/
theorem PaperStandardModelSupportSurfaceStatement
  {UVY LowY WY : Type}
  {UVE LowE WE : Type}
  {C E : Type}
  (DY : YukawaMassTransportData UVY LowY WY)
  (DE : EMCouplingTransportData UVE LowE WE)
  (DA : AnomalyYukawaData C)
  (DX : EquivalenceExhaustionData E)
  (RelevantY : (LowY → Prop) → Prop)
  (RelevantE : (LowE → Prop) → Prop)
  (hY_transport :
    ∀ u : UVY,
      DY.lowWitness (DY.transport u) = DY.uvWitness u)
  (hY_complete :
    witness_complete DY RelevantY)
  (hE_transport :
    ∀ u : UVE,
      DE.lowWitness (DE.transport u) = DE.uvWitness u)
  (hE_complete :
    em_witness_complete DE RelevantE)
  (hA_toYukawa :
    ∀ c : C, DA.anomalyFree c → DA.yukawaRealizable c)
  (hA_toAnomaly :
    ∀ c : C, DA.yukawaRealizable c → DA.anomalyFree c)
  (hX_exhaust :
    ∀ e : E,
      ¬ DX.admissible e ∨ DX.reintroducesKnownFailure e) :
  (∀ P : LowY → Prop,
    RelevantY P →
    ∀ u₁ u₂ : UVY,
      DY.uvWitness u₁ = DY.uvWitness u₂ →
      (P (DY.transport u₁) ↔ P (DY.transport u₂))) ∧
  ¬ independent_low_energy_yukawa_degree DY RelevantY ∧
  (∀ P : LowE → Prop,
    RelevantE P →
    ∀ u₁ u₂ : UVE,
      DE.uvWitness u₁ = DE.uvWitness u₂ →
      (P (DE.transport u₁) ↔ P (DE.transport u₂))) ∧
  ¬ independent_em_coupling_degree DE RelevantE ∧
  (∀ c : C, DA.anomalyFree c ↔ DA.yukawaRealizable c) ∧
  ¬ anomaly_yukawa_split DA ∧
  (∀ e : E, ¬ genuine_new_equivalence_completion DX e) ∧
  ¬ ∃ e : E, genuine_new_equivalence_completion DX e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      PaperFermionYukawaMassEquivalenceStatement
        DY
        RelevantY
        hY_transport
        hY_complete
  · exact
      PaperNoIndependentYukawaDegreeStatement
        DY
        RelevantY
        hY_transport
        hY_complete
  · exact
      PaperElectroweakElectromagneticCouplingEquivalenceStatement
        DE
        RelevantE
        hE_transport
        hE_complete
  · exact
      PaperNoIndependentEMCouplingDegreeStatement
        DE
        RelevantE
        hE_transport
        hE_complete
  · exact
      PaperAnomalyYukawaEquivalenceStatement
        DA
        hA_toYukawa
        hA_toAnomaly
  · exact
      PaperNoAnomalyYukawaSplitStatement
        DA
        hA_toYukawa
        hA_toAnomaly
  · exact
      PaperEquivalenceExhaustionStatement
        DX
        hX_exhaust
  · exact
      PaperEquivalenceSpaceClosureStatement
        DX
        hX_exhaust

end MaleyLean