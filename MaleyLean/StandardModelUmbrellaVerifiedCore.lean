import MaleyLean.StandardModelStructuralMetaClosureStatements
import MaleyLean.StandardModelDerivedWitnessBundle
import MaleyLean.ChargedCurrentPaperStatements
import MaleyLean.ChargedCurrentDerivedPaperStatements
import MaleyLean.QCDCPoddCleanPaperStatements
import MaleyLean.EquivalenceExhaustionPaperStatements

namespace MaleyLean

/--
Aggregate verified-core bundle for the current Standard Model umbrella layer.

This package combines:
- the generic structural/meta-closure core
- the current charged-current support surface
- the clean CP-odd QCD support surface
- the strengthened shared-witness bundle for Papers 3 through 11
- the current equivalence-exhaustion closure surface

It is still an honest verified core rather than a full field-level encoding of
the umbrella manuscript.
-/
structure StandardModelUmbrellaVerifiedCoreBundle
    {alpha beta : Type}
    {CY WY : Type}
    {CE WE : Type}
    {CN MN RN : Type}
    {CL WL : Type}
    {CA WA : Type}
    {CU WU : Type}
    {CR WR : Type}
    {CF WF : Type}
    {CH WH : Type}
    {UVCC LowCC ExtCC WCC VCC : Type}
    {GQ UVQ WQ : Type}
    {GCC : Type}
    {EX : Type}
    [Mul GCC] [Div GCC] [OfNat GCC 2] [OfNat GCC 4] [OfNat GCC 8] [One GCC]
    (A : RedescriptionAction alpha)
    (B : InvariantBundle alpha)
    (S : System alpha)
    (rel : alpha -> alpha -> Prop)
    (Admitted : alpha -> Prop)
    (licensed_same_scope_continuation : Redescription alpha alpha -> Prop)
    (preserves_relevant_invariants : alpha -> Redescription alpha alpha -> Prop)
    (QD I1 I2 : alpha -> Prop)
    (S2 : System beta)
    (f : Redescription alpha beta)
    (g : Redescription beta beta)
    (DY : YukawaMassWitnessData CY WY)
    (DE : EMCouplingWitnessData CE WE)
    (DN : NeutrinoWitnessPairData CN MN RN)
    (DL : LongitudinalGoldstoneWitnessData CL WL)
    (DA : AnomalyYukawaWitnessData CA WA)
    (DU : UnitaryMixingWitnessData CU WU)
    (DR : RephasingWitnessData CR WR)
    (DF : FCNCWitnessData CF WF)
    (DH : HyperchargeWitnessData CH WH)
    (DCC : ChargedCurrentTransportData UVCC LowCC ExtCC WCC VCC)
    (opsQ : CPoddPhaseOpsClean GQ)
    (DQCD : QCDCPoddDataClean UVQ WQ)
    (DX : EquivalenceExhaustionData EX) where
  structural_meta_closure :
    rel_transport_closure_interface B rel /\
    same_target_right_transport_interface B rel /\
    (forall a : alpha,
      Not (standing S a) ->
      Not (reuse_stably_admissible
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)) /\
    lawfully_equivalent_interiors I1 I2 /\
    lawfully_equivalent_interiors QD (fun x => standing S x) /\
    (forall (T : Redescription alpha alpha) (a : alpha),
      Not (standing S a) ->
      (standing S (T a) -> a = T a) ->
      Not (standing S (T a))) /\
    (forall (T : Redescription alpha alpha) (a : alpha),
      Not (standing S a) ->
      standing S (T a) ->
      T a = a ->
      False) /\
    irrecoverable_failure S S2 (compose_redescription f g)
  derived_witness_bundle :
    StandardModelDerivedWitnessBundle
      DY DE DN DL DA DU DR DF DH
  paper1_restricted_collapse :
    forall (Relevant : (LowCC -> Prop) -> Prop)
      (_h_transport : forall u : UVCC,
        DCC.lowRestrictedWitness (DCC.transportRestricted u) =
          DCC.uvRestrictedWitness u)
      (_h_complete : restricted_cc_witness_complete DCC Relevant),
      forall P : LowCC -> Prop,
        Relevant P ->
        forall u1 u2 : UVCC,
          DCC.uvRestrictedWitness u1 = DCC.uvRestrictedWitness u2 ->
          (P (DCC.transportRestricted u1) <-> P (DCC.transportRestricted u2))
  paper1_no_independent_restricted_degree :
    forall (Relevant : (LowCC -> Prop) -> Prop)
      (_h_transport : forall u : UVCC,
        DCC.lowRestrictedWitness (DCC.transportRestricted u) =
          DCC.uvRestrictedWitness u)
      (_h_complete : restricted_cc_witness_complete DCC Relevant),
      Not (independent_restricted_cc_degree DCC Relevant)
  paper1_extended_scope_witness :
    forall (_h_transport_ext : forall u : UVCC,
      DCC.extExtendedWitness (DCC.transportExtended u) =
        DCC.uvExtendedWitness u),
      forall u1 u2 : UVCC,
        DCC.uvExtendedWitness u1 = DCC.uvExtendedWitness u2 ->
        DCC.extExtendedWitness (DCC.transportExtended u1) =
          DCC.extExtendedWitness (DCC.transportExtended u2)
  paper1_formula_chain :
    forall g2sq vsq mWsq gf : GCC,
      mWsq = massFromGaugeCoupling g2sq vsq ->
      gf = gfFromMediator g2sq mWsq ->
      gfFromMediator g2sq (massFromGaugeCoupling g2sq vsq) = gfFromVev vsq ->
      gf = gfFromVev vsq
  paper1_extended_witness_reconstruction :
    forall gf invMassSq : GCC,
      (c6FromGF gf, c8FromGFAndInvMass gf invMassSq) =
        (gf, gf * invMassSq)
  paper2_bar_theta_invariant :
    forall delta theta argdetM : GQ,
      barThetaClean
          opsQ
          (thetaAfterRephasingClean opsQ delta theta)
          (argdetAfterRephasingClean opsQ delta argdetM)
        =
          barThetaClean opsQ theta argdetM
  paper2_collapse :
    forall P : UVQ -> Prop,
      (forall u1 u2 : UVQ,
        DQCD.cpOddWitness u1 = DQCD.cpOddWitness u2 ->
        (P u1 <-> P u2)) ->
      forall u1 u2 : UVQ,
        DQCD.cpOddWitness u1 = DQCD.cpOddWitness u2 ->
        (P u1 <-> P u2)
  paper2_no_split :
    forall Observable : UVQ -> Prop,
      (forall u1 u2 : UVQ,
        DQCD.cpOddWitness u1 = DQCD.cpOddWitness u2 ->
        (Observable u1 <-> Observable u2)) ->
      forall u1 u2 : UVQ,
        DQCD.cpOddWitness u1 = DQCD.cpOddWitness u2 ->
        (Observable u1 <-> Observable u2)
  paper12_exhaustion :
    (forall e : EX,
      Not (DX.admissible e) \/ DX.reintroducesKnownFailure e) ->
    forall e : EX, Not (genuine_new_equivalence_completion DX e)
  paper12_closure :
    (forall e : EX,
      Not (DX.admissible e) \/ DX.reintroducesKnownFailure e) ->
    Not (Exists (fun e : EX => genuine_new_equivalence_completion DX e))

/--
Aggregate paper-facing theorem for the current umbrella verified core.
-/
def PaperStandardModelUmbrellaVerifiedCoreStatement
    {alpha beta : Type}
    {CY WY : Type}
    {CE WE : Type}
    {CN MN RN : Type}
    {CL WL : Type}
    {CA WA : Type}
    {CU WU : Type}
    {CR WR : Type}
    {CF WF : Type}
    {CH WH : Type}
    {UVCC LowCC ExtCC WCC VCC : Type}
    {GQ UVQ WQ : Type}
    {GCC : Type}
    {EX : Type}
    [Mul GCC] [Div GCC] [OfNat GCC 2] [OfNat GCC 4] [OfNat GCC 8] [One GCC]
    (A : RedescriptionAction alpha)
    (B : InvariantBundle alpha)
    (S : System alpha)
    (rel : alpha -> alpha -> Prop)
    (Admitted : alpha -> Prop)
    (licensed_same_scope_continuation : Redescription alpha alpha -> Prop)
    (preserves_relevant_invariants : alpha -> Redescription alpha alpha -> Prop)
    (QD I1 I2 : alpha -> Prop)
    (S2 : System beta)
    (f : Redescription alpha beta)
    (g : Redescription beta beta)
    (DY : YukawaMassWitnessData CY WY)
    (DE : EMCouplingWitnessData CE WE)
    (DN : NeutrinoWitnessPairData CN MN RN)
    (DL : LongitudinalGoldstoneWitnessData CL WL)
    (DA : AnomalyYukawaWitnessData CA WA)
    (DU : UnitaryMixingWitnessData CU WU)
    (DR : RephasingWitnessData CR WR)
    (DF : FCNCWitnessData CF WF)
    (DH : HyperchargeWitnessData CH WH)
    (DCC : ChargedCurrentTransportData UVCC LowCC ExtCC WCC VCC)
    (opsQ : CPoddPhaseOpsClean GQ)
    (DQCD : QCDCPoddDataClean UVQ WQ)
    (DX : EquivalenceExhaustionData EX)
    (h_orbit : orbit_agrees_with_invariants A B)
    (h_transport : action_transport_closure A rel)
    (h_ext :
      forall a : alpha,
        reuse_stably_admissible
          Admitted
          licensed_same_scope_continuation
          preserves_relevant_invariants
          a ->
        standing S a)
    (h_toStanding : forall a : alpha, QD a -> standing S a)
    (h_fromStanding : forall a : alpha, standing S a -> QD a)
    (hI1 : forall a, I1 a -> standing S a)
    (hI2 : forall a, I2 a -> standing S a)
    (h_complete_I1 : forall a, standing S a -> I1 a)
    (h_complete_I2 : forall a, standing S a -> I2 a)
    (hirr : irrecoverable_failure S S2 f)
    (hsp : standing_preserving_redescription S2 S2 g)
    (hY_mass : forall c : CY, DY.massWitness c = DY.witness c)
    (hY_yukawa : forall c : CY, DY.yukawaWitness c = DY.witness c)
    (hE_ew : forall c : CE, DE.ewWitness c = DE.witness c)
    (hE_em : forall c : CE, DE.emWitness c = DE.witness c)
    (hN_mass : forall c : CN, DN.sourceMass c = DN.witnessMass c)
    (hN_mix : forall c : CN, DN.sourceMix c = DN.witnessMix c)
    (hL_long : forall c : CL, DL.longitudinalWitness c = DL.witness c)
    (hL_gold : forall c : CL, DL.goldstoneWitness c = DL.witness c)
    (hA_anom : forall c : CA, DA.anomalyWitness c = DA.witness c)
    (hA_yuk : forall c : CA, DA.yukawaWitness c = DA.witness c)
    (hU_op : forall c : CU, DU.operatorWitness c = DU.witness c)
    (hU_res : forall c : CU, DU.residualWitness c = DU.witness c)
    (hR_op : forall c : CR, DR.operatorWitness c = DR.witness c)
    (hR_res : forall c : CR, DR.residualWitness c = DR.witness c)
    (hF_align : forall c : CF, DF.alignmentWitness c = DF.witness c)
    (hF_fcnc : forall c : CF, DF.fcncWitness c = DF.witness c)
    (hH_shared :
      forall c : CH,
        DH.normalizedByWitness (DH.witness c) <->
          DH.chargeQuantizedByWitness (DH.witness c)) :
    StandardModelUmbrellaVerifiedCoreBundle
      A B S rel Admitted licensed_same_scope_continuation preserves_relevant_invariants
      QD I1 I2 S2 f g DY DE DN DL DA DU DR DF DH DCC opsQ DQCD DX := by
  refine
    { structural_meta_closure := by
        exact
          PaperStandardModelStructuralMetaClosureStatement
            A B S rel Admitted licensed_same_scope_continuation preserves_relevant_invariants
            QD I1 I2 S2 f g
            h_orbit h_transport h_ext h_toStanding h_fromStanding
            hI1 hI2 h_complete_I1 h_complete_I2 hirr hsp
      derived_witness_bundle := by
        exact
          PaperStandardModelDerivedWitnessBundleStatement
            DY DE DN DL DA DU DR DF DH
            hY_mass hY_yukawa hE_ew hE_em hN_mass hN_mix hL_long hL_gold
            hA_anom hA_yuk hU_op hU_res hR_op hR_res hF_align hF_fcnc hH_shared
      paper1_restricted_collapse := by
        intro Relevant h_transport_cc h_complete_cc
        exact
          PaperChargedCurrentRestrictedCollapseStatement
            DCC
            Relevant
            h_transport_cc
            h_complete_cc
      paper1_no_independent_restricted_degree := by
        intro Relevant h_transport_cc h_complete_cc
        exact
          PaperNoIndependentRestrictedChargedCurrentDegreeStatement
            DCC
            Relevant
            h_transport_cc
            h_complete_cc
      paper1_extended_scope_witness := by
        intro h_transport_ext
        exact
          PaperChargedCurrentExtendedScopeWitnessStatement
            DCC
            h_transport_ext
      paper1_formula_chain := by
        intro g2sq vsq mWsq gf h_mW h_match h_collapse
        exact
          PaperChargedCurrentRestrictedFormulaChainStatement
            g2sq vsq mWsq gf h_mW h_match h_collapse
      paper1_extended_witness_reconstruction := by
        intro gf invMassSq
        exact
          PaperChargedCurrentExtendedWitnessReconstructionStatement
            gf invMassSq
      paper2_bar_theta_invariant := by
        intro delta theta argdetM
        exact
          PaperQCDBarThetaInvariantCleanStatement
            opsQ delta theta argdetM
      paper2_collapse := by
        intro P h_complete u1 u2 hEq
        exact
          PaperQCDCPoddCollapseCleanStatement
            DQCD P h_complete u1 u2 hEq
      paper2_no_split := by
        intro Observable h_complete u1 u2 hEq
        exact
          PaperNoQCDCPoddObservableSplitCleanStatement
            DQCD Observable h_complete u1 u2 hEq
      paper12_exhaustion := by
        intro h_exhaust
        exact PaperEquivalenceExhaustionStatement DX h_exhaust
      paper12_closure := by
        intro h_exhaust
        exact PaperEquivalenceSpaceClosureStatement DX h_exhaust }

end MaleyLean
