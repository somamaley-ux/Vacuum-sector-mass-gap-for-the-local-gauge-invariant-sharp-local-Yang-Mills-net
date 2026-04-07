import MaleyLean.AmetricCollapseTheorem
import MaleyLean.ClosurePropagation
import MaleyLean.ChainComposition
import MaleyLean.ChainIrrecoverability
import MaleyLean.NoDeferredRepair
import MaleyLean.NoStagedRepair
import MaleyLean.NoFiniteRepair
import MaleyLean.Bivalence
import MaleyLean.BivalenceUniqueness

namespace MaleyLean

theorem PaperAmetricCollapseStatement
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂) :
  [DecidablePred (fun x : α => standing S x)] →
  (∃ x, m₁ x ≠ m₂ x) ↔ (∃ x, standing S x ∧ m₁ x ≠ m₂ x) := by
  intro _
  constructor
  · intro hdiff
    rcases hdiff with ⟨x, hneqx⟩
    by_cases hx : standing S x
    · exact ⟨x, hx, hneqx⟩
    · have hm1 : m₁ x = 0 := h₁ x hx
      have hm2 : m₂ x = 0 := h₂ x hx
      exact False.elim (hneqx (hm1.trans hm2.symm))
  · intro hsupp
    rcases hsupp with ⟨x, hx, hneqx⟩
    exact ⟨x, hneqx⟩

theorem PaperStandingContentStatement
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂) :
  [DecidablePred (fun x : α => standing S x)] →
  (∀ x, m₁ x = m₂ x) ↔ ∀ x, standing S x → m₁ x = m₂ x := by
  intro _
  constructor
  · intro hEq x hx
    exact hEq x
  · intro hStanding
    intro x
    by_cases hx : standing S x
    · exact hStanding x hx
    · exact (h₁ x hx).trans (h₂ x hx).symm

theorem PaperFailureRegionContentStatement
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hx : failure_region S x) :
  m₁ x = m₂ x := by
  exact failure_region_supports_no_admissible_metric_content S m₁ m₂ h₁ h₂ x hx

theorem PaperIrrecoverabilityMetricInvarianceStatement
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m₁ m₂ : Metric β)
  (h₁ : ametric_boundary S₂ m₁)
  (h₂ : ametric_boundary S₂ m₂)
  (hirr : irrecoverable_failure S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m₁ (f x) = 0 ∧ m₂ (f x) = 0 := by
  exact witnessed_failure_collapses_all_admissible_metric_content S₁ S₂ f m₁ m₂ h₁ h₂ hirr

theorem PaperStandingPreservationCompositionStatement
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

theorem PaperClosurePropagationStatement
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

theorem PaperIntermediateContainmentExclusionStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  exact intermediate_mapping_cannot_contain_failure S₁ S₂ S₃ f g hirr hsp

theorem PaperCompositeUnusabilityDecompositionStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hbad : unusable_redescription S₁ S₃ (compose_redescription f g)) :
  (redescription_legal S₁ S₂ f → unusable_redescription S₂ S₃ g) ∧
  (redescription_legal S₂ S₃ g → unusable_redescription S₁ S₂ f) := by
  constructor
  · intro hf hg
    exact hbad (composition_of_legal_redescriptions_is_legal S₁ S₂ S₃ f g hf hg)
  · intro hg hf
    exact hbad (composition_of_legal_redescriptions_is_legal S₁ S₂ S₃ f g hf hg)

theorem PaperNoDeferredRepairTwoStepStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact no_deferred_repair_two_step S₁ S₂ S₃ f g hirr hsp

theorem PaperNoDeferredRepairTwoStepBlocksLegalityStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  exact no_deferred_repair_two_step_blocks_legality S₁ S₂ S₃ f g hirr hsp

theorem PaperNoDeferredRepairTwoStepUnusabilityStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  unusable_redescription S₁ S₃ (compose_redescription f g) := by
  exact no_deferred_repair_two_step_yields_unusability S₁ S₂ S₃ f g hirr hsp

theorem PaperNoStagedRepairThreeStepStatement
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
  exact no_staged_repair_three_step S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperNoStagedRepairThreeStepBlocksLegalityStatement
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
  exact no_staged_repair_three_step_blocks_legality S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperNoStagedRepairThreeStepUnusabilityStatement
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

theorem PaperNoFiniteRepairFourStepStatement
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
  exact no_finite_repair_four_step S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem PaperNoFiniteRepairFourStepBlocksLegalityStatement
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

theorem PaperNoFiniteRepairFourStepUnusabilityStatement
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

theorem PaperChainThreeCompositionStandingPreservationStatement
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hf : standing_preserving_redescription S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  standing_preserving_redescription S₁ S₄
    (compose_three_redescriptions f g h) := by
  exact
    compose_three_redescriptions_is_standing_preserving
      S₁ S₂ S₃ S₄ f g h hf hg hh

theorem PaperChainFourCompositionStandingPreservationStatement
  {α β γ δ ε : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ) (S₅ : System ε)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (k : Redescription δ ε)
  (hf : standing_preserving_redescription S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h)
  (hk : standing_preserving_redescription S₄ S₅ k) :
  standing_preserving_redescription S₁ S₅
    (compose_four_redescriptions f g h k) := by
  exact
    compose_four_redescriptions_is_standing_preserving
      S₁ S₂ S₃ S₄ S₅ f g h k hf hg hh hk

theorem PaperChainThreeIrrecoverabilityStatement
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  irrecoverable_failure S₁ S₄
    (compose_three_redescriptions f g h) := by
  exact compose_three_redescriptions_preserves_irrecoverability S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperChainThreeBlocksLegalityStatement
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  ¬ redescription_legal S₁ S₄
    (compose_three_redescriptions f g h) := by
  exact compose_three_redescriptions_blocks_legality S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperChainThreeYieldsUnusabilityStatement
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  unusable_redescription S₁ S₄
    (compose_three_redescriptions f g h) := by
  exact compose_three_redescriptions_yields_unusability S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperChainFourIrrecoverabilityStatement
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
    (compose_four_redescriptions f g h k) := by
  exact
    compose_four_redescriptions_preserves_irrecoverability
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem PaperChainFourBlocksLegalityStatement
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
    (compose_four_redescriptions f g h k) := by
  exact
    compose_four_redescriptions_blocks_legality
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem PaperChainFourYieldsUnusabilityStatement
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
    (compose_four_redescriptions f g h k) := by
  exact
    compose_four_redescriptions_yields_unusability
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem PaperStandingBivalenceStatement
  {α : Type}
  (S : System α)
  (x : α) :
  [DecidablePred (fun x : α => standing S x)] →
  (standing S x ∨ failure_region S x) ∧
  ¬ (standing S x ∧ failure_region S x) := by
  intro _
  constructor
  · by_cases hx : standing S x
    · exact Or.inl hx
    · exact Or.inr hx
  · exact not_standing_and_failure S x

theorem PaperBivalenceUniquenessStatement
  {α : Type}
  (S : System α)
  (P : α → Prop)
  (hP : ∀ x, P x ↔ standing S x ∨ failure_region S x) :
  [DecidablePred (fun x : α => standing S x)] →
  ∀ x, P x ↔ True := by
  intro _
  intro x
  constructor
  · intro _
    trivial
  · intro _
    by_cases hx : standing S x
    · exact (hP x).2 (Or.inl hx)
    · exact (hP x).2 (Or.inr hx)

end MaleyLean
