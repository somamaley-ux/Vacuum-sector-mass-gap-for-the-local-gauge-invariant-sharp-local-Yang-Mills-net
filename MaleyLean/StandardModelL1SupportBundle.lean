import MaleyLean.StandardModelDerivedWitnessBundle
import MaleyLean.ChargedCurrentPaperStatements
import MaleyLean.ChargedCurrentDerivedPaperStatements
import MaleyLean.QCDCPoddCleanPaperStatements
import MaleyLean.EquivalenceExhaustionPaperStatements

namespace MaleyLean

/--
Aggregate bundle for the current L1 support stack alone.

This isolates Papers 1 through 12 from the broader structural/meta-closure
machinery so the support-paper layer has its own integrated checkpoint.
-/
structure StandardModelL1SupportBundle
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
  paper3_to_11_bundle :
    StandardModelDerivedWitnessBundle
      DY DE DN DL DA DU DR DF DH
  paper12_exhaustion :
    (forall e : EX,
      Not (DX.admissible e) \/ DX.reintroducesKnownFailure e) ->
    forall e : EX, Not (genuine_new_equivalence_completion DX e)
  paper12_closure :
    (forall e : EX,
      Not (DX.admissible e) \/ DX.reintroducesKnownFailure e) ->
    Not (Exists (fun e : EX => genuine_new_equivalence_completion DX e))

/--
Aggregate paper-facing theorem for the current L1 support stack.
-/
def PaperStandardModelL1SupportBundleStatement
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
    StandardModelL1SupportBundle
      DY DE DN DL DA DU DR DF DH DCC opsQ DQCD DX := by
  refine
    { paper1_restricted_collapse := by
        intro Relevant h_transport_cc h_complete_cc
        exact
          PaperChargedCurrentRestrictedCollapseStatement
            DCC Relevant h_transport_cc h_complete_cc
      paper1_no_independent_restricted_degree := by
        intro Relevant h_transport_cc h_complete_cc
        exact
          PaperNoIndependentRestrictedChargedCurrentDegreeStatement
            DCC Relevant h_transport_cc h_complete_cc
      paper1_extended_scope_witness := by
        intro h_transport_ext
        exact
          PaperChargedCurrentExtendedScopeWitnessStatement
            DCC h_transport_ext
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
      paper3_to_11_bundle := by
        exact
          PaperStandardModelDerivedWitnessBundleStatement
            DY DE DN DL DA DU DR DF DH
            hY_mass hY_yukawa hE_ew hE_em hN_mass hN_mix hL_long hL_gold
            hA_anom hA_yuk hU_op hU_res hR_op hR_res hF_align hF_fcnc hH_shared
      paper12_exhaustion := by
        intro h_exhaust
        exact PaperEquivalenceExhaustionStatement DX h_exhaust
      paper12_closure := by
        intro h_exhaust
        exact PaperEquivalenceSpaceClosureStatement DX h_exhaust }

end MaleyLean
