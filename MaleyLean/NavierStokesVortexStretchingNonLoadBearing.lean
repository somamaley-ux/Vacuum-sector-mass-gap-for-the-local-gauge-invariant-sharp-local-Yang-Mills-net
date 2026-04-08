import MaleyLean.NavierStokesPrimitiveBridge
import MaleyLean.NavierStokesContinuationBoundary
import MaleyLean.NavierStokesVerbatimDependencySpineSimple

namespace MaleyLean

/--
Vortex-stretching non-load-bearing packet for the primitive Navier--Stokes
route.

The point of this layer is not to solve a missing PDE estimate. It is to state
that once vortex-stretching observables are typed as bookkeeping-visible only,
they cannot also function as same-scope continuation gates.
-/
def vortex_stretching_is_non_load_bearing
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  metric_divergence_skin_only S ->
  forall q : Quantity,
    S.metricQuantity q ->
    S.quotientVisibleWitnessBookkeeping q \/ ¬ S.illicitMetricGate q

def vortex_stretching_cannot_decide_continuation
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  metric_divergence_skin_only S ->
  ¬ vortex_stretching_anomaly_boundary S

def vortex_stretching_requires_hidden_second_gate
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  vortex_stretching_anomaly_boundary S ->
  ¬ metric_divergence_skin_only S

theorem PaperVortexStretchingNonLoadBearingStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) :
  vortex_stretching_is_non_load_bearing S := by
  intro hskin q hq
  exact hskin q hq

theorem PaperVortexStretchingCannotDecideContinuationStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) :
  vortex_stretching_cannot_decide_continuation S := by
  intro hskin hanom
  exact PaperPrimitiveToPDEBridgeBoundaryStatement S hskin hanom

theorem PaperVortexStretchingRequiresHiddenSecondGateStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) :
  vortex_stretching_requires_hidden_second_gate S := by
  intro hanom hskin
  exact PaperPrimitiveToPDEBridgeBoundaryStatement S hskin hanom

theorem PaperVerbatimFailureTitleMatchesNonLoadBearingBoundaryStatement :
  verbatim_theorem_is_named_failure_boundary_simple .pointwiseVortexStretchingGateCollapse := by
  exact PaperVerbatimNamedFailureTitleSimpleStatement

theorem PaperEndpointTitlesRemainDownstreamOfNonLoadBearingBoundaryStatement :
  verbatim_theorem_is_endpoint_downstream_simple .officialPeriodicTheoremOnT3 /\
  verbatim_theorem_is_endpoint_downstream_simple .noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier := by
  exact PaperVerbatimEndpointTitlesSimpleStatement

end MaleyLean
