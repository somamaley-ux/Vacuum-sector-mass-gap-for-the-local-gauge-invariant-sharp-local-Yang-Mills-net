import MaleyLean.NavierStokesVortexStretchingNonLoadBearing

namespace MaleyLean

/--
No-hidden-scope-change packet for the primitive Navier--Stokes route.

This layer makes the manuscript interpretation explicit: if a vortex-stretching
observable is used as a continuation-deciding object, then under skin-only
typing it must either remain bookkeeping-visible or collapse into a hidden
second gate. There is no lawful same-scope rescue through that seam.
-/
def vortex_stretching_illicit_gate_is_bookkeeping_visible
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  metric_divergence_skin_only S ->
  forall q : Quantity,
    S.metricQuantity q ->
    S.illicitMetricGate q ->
    S.quotientVisibleWitnessBookkeeping q

def no_same_scope_vortex_rescue
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  metric_divergence_skin_only S ->
  forall q : Quantity,
    S.metricQuantity q ->
    S.illicitMetricGate q ->
    False

def vortex_rescue_requires_scope_change_or_hidden_second_gate
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  metric_divergence_skin_only S ->
  forall q : Quantity,
    S.metricQuantity q ->
    S.illicitMetricGate q ->
    S.quotientVisibleWitnessBookkeeping q

theorem PaperIllicitVortexGateIsBookkeepingVisibleStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) :
  vortex_stretching_illicit_gate_is_bookkeeping_visible S := by
  intro hskin q hq hillicit
  rcases hskin q hq with hbook | hnotgate
  · exact hbook
  · exact False.elim (hnotgate hillicit)

theorem PaperNoSameScopeVortexRescueStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (hload :
    forall q : Quantity,
      S.metricQuantity q ->
      S.quotientVisibleWitnessBookkeeping q ->
      False) :
  no_same_scope_vortex_rescue S := by
  intro hskin q hq hillicit
  have hbook : S.quotientVisibleWitnessBookkeeping q :=
    PaperIllicitVortexGateIsBookkeepingVisibleStatement S hskin q hq hillicit
  exact hload q hq hbook

theorem PaperVortexRescueRequiresScopeChangeOrHiddenSecondGateStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) :
  vortex_rescue_requires_scope_change_or_hidden_second_gate S := by
  intro hskin q hq hillicit
  exact PaperIllicitVortexGateIsBookkeepingVisibleStatement S hskin q hq hillicit

theorem PaperNoHiddenScopeChangeMatchesFailureBoundaryStatement :
  verbatim_theorem_is_named_failure_boundary_simple .pointwiseVortexStretchingGateCollapse := by
  exact PaperVerbatimFailureTitleMatchesNonLoadBearingBoundaryStatement

end MaleyLean
