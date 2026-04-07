import MaleyLean.YukawaMassDerivedPaperStatements
import MaleyLean.EMCouplingDerivedPaperStatements
import MaleyLean.NeutrinoMixingDerivedPaperStatements
import MaleyLean.LongitudinalGoldstoneDerivedPaperStatements
import MaleyLean.AnomalyYukawaDerivedPaperStatements
import MaleyLean.UnitaryMixingDerivedPaperStatements
import MaleyLean.RephasingDerivedPaperStatements
import MaleyLean.FCNCDerivedPaperStatements
import MaleyLean.HyperchargeDerivedPaperStatements

namespace MaleyLean

/--
Aggregate bundle for the strengthened shared-witness layers currently available
for the Standard Model L1 support stack.

This package is intentionally narrower than the full support surface: it bundles
the derived witness-collapse layers for Papers 3 through 11.
-/
structure StandardModelDerivedWitnessBundle
    {CY WY : Type}
    {CE WE : Type}
    {CN MN RN : Type}
    {CL WL : Type}
    {CA WA : Type}
    {CU WU : Type}
    {CR WR : Type}
    {CF WF : Type}
    {CH WH : Type}
    (DY : YukawaMassWitnessData CY WY)
    (DE : EMCouplingWitnessData CE WE)
    (DN : NeutrinoWitnessPairData CN MN RN)
    (DL : LongitudinalGoldstoneWitnessData CL WL)
    (DA : AnomalyYukawaWitnessData CA WA)
    (DU : UnitaryMixingWitnessData CU WU)
    (DR : RephasingWitnessData CR WR)
    (DF : FCNCWitnessData CF WF)
    (DH : HyperchargeWitnessData CH WH) where
  paper3_shared :
    ∀ c : CY, DY.massWitness c = DY.yukawaWitness c
  paper3_no_split :
    ¬ ∃ c : CY, DY.massWitness c ≠ DY.yukawaWitness c
  paper4_shared :
    ∀ c : CE, DE.ewWitness c = DE.emWitness c
  paper4_no_split :
    ¬ ∃ c : CE, DE.ewWitness c ≠ DE.emWitness c
  paper5_shared :
    ∀ c : CN,
      (DN.sourceMass c, DN.sourceMix c) =
        (DN.witnessMass c, DN.witnessMix c)
  paper5_no_split :
    ¬ ∃ c : CN,
      (DN.sourceMass c, DN.sourceMix c) ≠
        (DN.witnessMass c, DN.witnessMix c)
  paper6_shared :
    ∀ c : CL, DL.longitudinalWitness c = DL.goldstoneWitness c
  paper6_no_split :
    ¬ ∃ c : CL, DL.longitudinalWitness c ≠ DL.goldstoneWitness c
  paper7_shared :
    ∀ c : CA, DA.anomalyWitness c = DA.yukawaWitness c
  paper7_no_split :
    ¬ ∃ c : CA, DA.anomalyWitness c ≠ DA.yukawaWitness c
  paper8_shared :
    ∀ c : CU, DU.operatorWitness c = DU.residualWitness c
  paper8_no_split :
    ¬ ∃ c : CU, DU.operatorWitness c ≠ DU.residualWitness c
  paper9_shared :
    ∀ c : CR, DR.operatorWitness c = DR.residualWitness c
  paper9_no_split :
    ¬ ∃ c : CR, DR.operatorWitness c ≠ DR.residualWitness c
  paper10_shared :
    ∀ c : CF, DF.alignmentWitness c = DF.fcncWitness c
  paper10_no_split :
    ¬ ∃ c : CF, DF.alignmentWitness c ≠ DF.fcncWitness c
  paper11_shared :
    ∀ c : CH,
      DH.normalizedByWitness (DH.witness c) ↔
        DH.chargeQuantizedByWitness (DH.witness c)
  paper11_no_split :
    ¬ ∃ c : CH,
        (DH.normalizedByWitness (DH.witness c) ∧
          ¬ DH.chargeQuantizedByWitness (DH.witness c)) ∨
        (DH.chargeQuantizedByWitness (DH.witness c) ∧
          ¬ DH.normalizedByWitness (DH.witness c))

/--
Aggregate paper-facing theorem bundling the strengthened shared-witness layers
for Papers 3 through 11.
-/
theorem PaperStandardModelDerivedWitnessBundleStatement
    {CY WY : Type}
    {CE WE : Type}
    {CN MN RN : Type}
    {CL WL : Type}
    {CA WA : Type}
    {CU WU : Type}
    {CR WR : Type}
    {CF WF : Type}
    {CH WH : Type}
    (DY : YukawaMassWitnessData CY WY)
    (DE : EMCouplingWitnessData CE WE)
    (DN : NeutrinoWitnessPairData CN MN RN)
    (DL : LongitudinalGoldstoneWitnessData CL WL)
    (DA : AnomalyYukawaWitnessData CA WA)
    (DU : UnitaryMixingWitnessData CU WU)
    (DR : RephasingWitnessData CR WR)
    (DF : FCNCWitnessData CF WF)
    (DH : HyperchargeWitnessData CH WH)
    (hY_mass : ∀ c : CY, DY.massWitness c = DY.witness c)
    (hY_yukawa : ∀ c : CY, DY.yukawaWitness c = DY.witness c)
    (hE_ew : ∀ c : CE, DE.ewWitness c = DE.witness c)
    (hE_em : ∀ c : CE, DE.emWitness c = DE.witness c)
    (hN_mass : ∀ c : CN, DN.sourceMass c = DN.witnessMass c)
    (hN_mix : ∀ c : CN, DN.sourceMix c = DN.witnessMix c)
    (hL_long : ∀ c : CL, DL.longitudinalWitness c = DL.witness c)
    (hL_gold : ∀ c : CL, DL.goldstoneWitness c = DL.witness c)
    (hA_anom : ∀ c : CA, DA.anomalyWitness c = DA.witness c)
    (hA_yuk : ∀ c : CA, DA.yukawaWitness c = DA.witness c)
    (hU_op : ∀ c : CU, DU.operatorWitness c = DU.witness c)
    (hU_res : ∀ c : CU, DU.residualWitness c = DU.witness c)
    (hR_op : ∀ c : CR, DR.operatorWitness c = DR.witness c)
    (hR_res : ∀ c : CR, DR.residualWitness c = DR.witness c)
    (hF_align : ∀ c : CF, DF.alignmentWitness c = DF.witness c)
    (hF_fcnc : ∀ c : CF, DF.fcncWitness c = DF.witness c)
    (hH_shared :
      ∀ c : CH,
        DH.normalizedByWitness (DH.witness c) ↔
          DH.chargeQuantizedByWitness (DH.witness c)) :
    StandardModelDerivedWitnessBundle
      DY DE DN DL DA DU DR DF DH := by
  refine
    { paper3_shared := by
        exact PaperYukawaMassSharedWitnessStatement DY hY_mass hY_yukawa
      paper3_no_split := by
        exact PaperNoYukawaMassWitnessSplitStatement DY hY_mass hY_yukawa
      paper4_shared := by
        exact PaperEMCouplingSharedWitnessStatement DE hE_ew hE_em
      paper4_no_split := by
        exact PaperNoEMCouplingWitnessSplitStatement DE hE_ew hE_em
      paper5_shared := by
        exact PaperNeutrinoSharedWitnessPairStatement DN hN_mass hN_mix
      paper5_no_split := by
        exact PaperNoNeutrinoWitnessPairSplitStatement DN hN_mass hN_mix
      paper6_shared := by
        exact PaperLongitudinalGoldstoneSharedWitnessStatement DL hL_long hL_gold
      paper6_no_split := by
        exact PaperNoLongitudinalGoldstoneWitnessSplitStatement DL hL_long hL_gold
      paper7_shared := by
        exact PaperAnomalyYukawaSharedWitnessStatement DA hA_anom hA_yuk
      paper7_no_split := by
        exact PaperNoAnomalyYukawaWitnessSplitStatement DA hA_anom hA_yuk
      paper8_shared := by
        exact PaperUnitaryMixingSharedWitnessStatement DU hU_op hU_res
      paper8_no_split := by
        exact PaperNoUnitaryMixingWitnessSplitStatement DU hU_op hU_res
      paper9_shared := by
        exact PaperRephasingSharedWitnessStatement DR hR_op hR_res
      paper9_no_split := by
        exact PaperNoRephasingWitnessSplitStatement DR hR_op hR_res
      paper10_shared := by
        exact PaperFCNCSharedWitnessStatement DF hF_align hF_fcnc
      paper10_no_split := by
        exact PaperNoFCNCWitnessSplitStatement DF hF_align hF_fcnc
      paper11_shared := by
        exact PaperHyperchargeSharedWitnessStatement DH hH_shared
      paper11_no_split := by
        exact PaperNoHyperchargeSharedWitnessSplitStatement DH hH_shared }

end MaleyLean
