import MaleyLean.AmetricCollapseTheorem
import MaleyLean.Bivalence
import MaleyLean.BivalenceUniqueness
import MaleyLean.Composition
import MaleyLean.Failure
import MaleyLean.NoRepair
import MaleyLean.Irrecoverability
import MaleyLean.StandingPreservation
import MaleyLean.ClosurePropagation
import MaleyLean.NoDeferredRepair
import MaleyLean.NoStagedRepair
import MaleyLean.NoFiniteRepair

namespace MaleyLean

theorem AmetricCollapseTheorem
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂) :
  (∃ x, m₁ x ≠ m₂ x) ↔ (∃ x, standing S x ∧ m₁ x ≠ m₂ x) := by
  exact ametric_collapse_theorem S m₁ m₂ h₁ h₂

theorem StandingRegionCarriesAllAdmissibleMetricContent
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂) :
  m₁ ≠ m₂ ↔ ∃ x, standing S x ∧ m₁ x ≠ m₂ x := by
  exact standing_region_carries_all_admissible_metric_content S m₁ m₂ h₁ h₂

theorem FailureRegionSupportsNoAdmissibleMetricContent
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hx : failure_region S x) :
  m₁ x = m₂ x := by
  exact failure_region_supports_no_admissible_metric_content S m₁ m₂ h₁ h₂ x hx

theorem IrrecoverabilityIsMetricInvariant
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m₁ m₂ : Metric β)
  (h₁ : ametric_boundary S₂ m₁)
  (h₂ : ametric_boundary S₂ m₂)
  (hirr : irrecoverable_failure S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m₁ (f x) = 0 ∧ m₂ (f x) = 0 := by
  exact irrecoverability_is_metric_invariant S₁ S₂ f m₁ m₂ h₁ h₂ hirr

theorem StandingPreservationCompositionTheorem
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hf : standing_preserving_redescription S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g) :
  standing_preserving_redescription S₁ S₃ (compose_redescription f g) := by
  exact
    composition_of_standing_preserving_redescriptions_is_standing_preserving
      S₁ S₂ S₃ f g hf hg

theorem ClosurePropagationTheorem
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact
    irrecoverable_failure_propagates_through_standing_preserving_composition
      S₁ S₂ S₃ f g hirr hsp

theorem IntermediateMappingCannotContainFailure
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  exact
    intermediate_mapping_cannot_contain_failure
      S₁ S₂ S₃ f g hirr hsp

theorem CompositeUnusabilityDecompositionTheorem
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hbad : unusable_redescription S₁ S₃ (compose_redescription f g)) :
  unusable_redescription S₁ S₂ f ∨ unusable_redescription S₂ S₃ g := by
  exact
    composite_unusability_implies_component_unusability
      S₁ S₂ S₃ f g hbad

theorem NoDeferredRepairTwoStepTheorem
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact
    no_deferred_repair_two_step
      S₁ S₂ S₃ f g hirr hsp

theorem NoDeferredRepairTwoStepBlocksLegalityTheorem
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  exact
    no_deferred_repair_two_step_blocks_legality
      S₁ S₂ S₃ f g hirr hsp

theorem NoDeferredRepairTwoStepYieldsUnusabilityTheorem
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  unusable_redescription S₁ S₃ (compose_redescription f g) := by
  exact
    no_deferred_repair_two_step_yields_unusability
      S₁ S₂ S₃ f g hirr hsp

theorem NoStagedRepairThreeStepTheorem
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  irrecoverable_failure S₁ S₄
    (compose_redescription f (compose_redescription g h)) := by
  exact
    no_staged_repair_three_step
      S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem NoStagedRepairThreeStepBlocksLegalityTheorem
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  ¬ redescription_legal S₁ S₄
    (compose_redescription f (compose_redescription g h)) := by
  exact
    no_staged_repair_three_step_blocks_legality
      S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem NoStagedRepairThreeStepYieldsUnusabilityTheorem
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  unusable_redescription S₁ S₄
    (compose_redescription f (compose_redescription g h)) := by
  exact
    no_staged_repair_three_step_yields_unusability
      S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem NoFiniteRepairFourStepTheorem
  {α β γ δ ε : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ) (S₅ : System ε)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (k : Redescription δ ε)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h)
  (hk : standing_preserving_redescription S₄ S₅ k) :
  irrecoverable_failure S₁ S₅
    (compose_redescription f (compose_redescription g (compose_redescription h k))) := by
  exact
    no_finite_repair_four_step
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem NoFiniteRepairFourStepBlocksLegalityTheorem
  {α β γ δ ε : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ) (S₅ : System ε)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (k : Redescription δ ε)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h)
  (hk : standing_preserving_redescription S₄ S₅ k) :
  ¬ redescription_legal S₁ S₅
    (compose_redescription f (compose_redescription g (compose_redescription h k))) := by
  exact
    no_finite_repair_four_step_blocks_legality
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem NoFiniteRepairFourStepYieldsUnusabilityTheorem
  {α β γ δ ε : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ) (S₅ : System ε)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (k : Redescription δ ε)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h)
  (hk : standing_preserving_redescription S₄ S₅ k) :
  unusable_redescription S₁ S₅
    (compose_redescription f (compose_redescription g (compose_redescription h k))) := by
  exact
    no_finite_repair_four_step_yields_unusability
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem StandingBivalenceTheorem
  {α : Type}
  (S : System α)
  (x : α) :
  (standing S x ∨ failure_region S x) ∧
  ¬ (standing S x ∧ failure_region S x) := by
  exact standing_failure_bivalence S x

theorem BivalenceUniquenessTheorem
  {α : Type}
  (S : System α)
  (P : α → Prop)
  (hP : ∀ x, P x ↔ standing S x ∨ failure_region S x) :
  P = fun _ => True := by
  exact bivalence_uniqueness_theorem S P hP

end MaleyLean
