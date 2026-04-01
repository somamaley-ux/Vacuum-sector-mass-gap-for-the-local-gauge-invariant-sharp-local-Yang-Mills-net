import MaleyLean.TheoremRegister
import MaleyLean.PaperStatements

namespace MaleyLean

theorem StabilizationCheckpoint_StandingPreservationComposition
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hf : standing_preserving_redescription S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g) :
  standing_preserving_redescription S₁ S₃ (compose_redescription f g) := by
  exact StandingPreservationCompositionTheorem S₁ S₂ S₃ f g hf hg

theorem StabilizationCheckpoint_ClosurePropagation
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact ClosurePropagationTheorem S₁ S₂ S₃ f g hirr hsp

theorem StabilizationCheckpoint_NoDeferredRepair
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  unusable_redescription S₁ S₃ (compose_redescription f g) := by
  exact NoDeferredRepairTwoStepYieldsUnusabilityTheorem S₁ S₂ S₃ f g hirr hsp

theorem StabilizationCheckpoint_NoStagedRepair
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
    NoStagedRepairThreeStepYieldsUnusabilityTheorem
      S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem StabilizationCheckpoint_NoFiniteRepair
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
    NoFiniteRepairFourStepYieldsUnusabilityTheorem
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem StabilizationCheckpoint_PaperSurfaceClosure
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact PaperClosurePropagationStatement S₁ S₂ S₃ f g hirr hsp

theorem StabilizationCheckpoint_PaperSurfaceFiniteRepair
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
    PaperNoFiniteRepairFourStepUnusabilityStatement
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

end MaleyLean
