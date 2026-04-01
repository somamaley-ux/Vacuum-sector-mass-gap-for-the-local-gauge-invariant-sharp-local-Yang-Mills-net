import MaleyLean.TheoremRegister

namespace MaleyLean

theorem PaperAmetricCollapseStatement
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂) :
  (∃ x, m₁ x ≠ m₂ x) ↔ (∃ x, standing S x ∧ m₁ x ≠ m₂ x) := by
  exact AmetricCollapseTheorem S m₁ m₂ h₁ h₂

theorem PaperStandingContentStatement
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂) :
  m₁ ≠ m₂ ↔ ∃ x, standing S x ∧ m₁ x ≠ m₂ x := by
  exact StandingRegionCarriesAllAdmissibleMetricContent S m₁ m₂ h₁ h₂

theorem PaperFailureRegionContentStatement
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hx : failure_region S x) :
  m₁ x = m₂ x := by
  exact FailureRegionSupportsNoAdmissibleMetricContent S m₁ m₂ h₁ h₂ x hx

theorem PaperIrrecoverabilityMetricInvarianceStatement
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m₁ m₂ : Metric β)
  (h₁ : ametric_boundary S₂ m₁)
  (h₂ : ametric_boundary S₂ m₂)
  (hirr : irrecoverable_failure S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m₁ (f x) = 0 ∧ m₂ (f x) = 0 := by
  exact IrrecoverabilityIsMetricInvariant S₁ S₂ f m₁ m₂ h₁ h₂ hirr

theorem PaperStandingPreservationCompositionStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hf : standing_preserving_redescription S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g) :
  standing_preserving_redescription S₁ S₃ (compose_redescription f g) := by
  exact StandingPreservationCompositionTheorem S₁ S₂ S₃ f g hf hg

theorem PaperClosurePropagationStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact ClosurePropagationTheorem S₁ S₂ S₃ f g hirr hsp

theorem PaperIntermediateContainmentExclusionStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  exact IntermediateMappingCannotContainFailure S₁ S₂ S₃ f g hirr hsp

theorem PaperCompositeUnusabilityDecompositionStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hbad : unusable_redescription S₁ S₃ (compose_redescription f g)) :
  unusable_redescription S₁ S₂ f ∨ unusable_redescription S₂ S₃ g := by
  exact CompositeUnusabilityDecompositionTheorem S₁ S₂ S₃ f g hbad

theorem PaperNoDeferredRepairTwoStepStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact NoDeferredRepairTwoStepTheorem S₁ S₂ S₃ f g hirr hsp

theorem PaperNoDeferredRepairTwoStepBlocksLegalityStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  exact NoDeferredRepairTwoStepBlocksLegalityTheorem S₁ S₂ S₃ f g hirr hsp

theorem PaperNoDeferredRepairTwoStepUnusabilityStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  unusable_redescription S₁ S₃ (compose_redescription f g) := by
  exact NoDeferredRepairTwoStepYieldsUnusabilityTheorem S₁ S₂ S₃ f g hirr hsp

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
  exact NoStagedRepairThreeStepTheorem S₁ S₂ S₃ S₄ f g h hirr hg hh

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
  exact NoStagedRepairThreeStepBlocksLegalityTheorem S₁ S₂ S₃ S₄ f g h hirr hg hh

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
  exact NoStagedRepairThreeStepYieldsUnusabilityTheorem S₁ S₂ S₃ S₄ f g h hirr hg hh

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
  exact NoFiniteRepairFourStepTheorem S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

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
  exact NoFiniteRepairFourStepBlocksLegalityTheorem
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
  exact NoFiniteRepairFourStepYieldsUnusabilityTheorem
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
  exact ChainThreeCompositionStandingPreservationTheorem
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
  exact ChainFourCompositionStandingPreservationTheorem
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
  exact ChainThreeIrrecoverabilityTheorem
    S₁ S₂ S₃ S₄ f g h hirr hg hh

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
  exact ChainThreeBlocksLegalityTheorem
    S₁ S₂ S₃ S₄ f g h hirr hg hh

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
  exact ChainThreeYieldsUnusabilityTheorem
    S₁ S₂ S₃ S₄ f g h hirr hg hh

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
  exact ChainFourIrrecoverabilityTheorem
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
  exact ChainFourBlocksLegalityTheorem
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
  exact ChainFourYieldsUnusabilityTheorem
    S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem PaperStandingBivalenceStatement
  {α : Type}
  (S : System α)
  (x : α) :
  (standing S x ∨ failure_region S x) ∧
  ¬ (standing S x ∧ failure_region S x) := by
  exact StandingBivalenceTheorem S x

theorem PaperBivalenceUniquenessStatement
  {α : Type}
  (S : System α)
  (P : α → Prop)
  (hP : ∀ x, P x ↔ standing S x ∨ failure_region S x) :
  P = fun _ => True := by
  exact BivalenceUniquenessTheorem S P hP

end MaleyLean
