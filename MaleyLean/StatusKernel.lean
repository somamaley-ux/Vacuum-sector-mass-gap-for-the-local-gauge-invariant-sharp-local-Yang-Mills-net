import MaleyLean.Core
import MaleyLean.StandingRefinement
import MaleyLean.StandingEmergenceBase

namespace MaleyLean

/-
Binary side of the admissibility interface.
Both standingBearing and admittedOnly lie on the positive side;
notAdmitted lies on the negative side.
-/
inductive StandingSide where
  | positive
  | negative
  deriving DecidableEq, Repr

def labelSide : StandingRefinementLabel → StandingSide
  | StandingRefinementLabel.standingBearing => StandingSide.positive
  | StandingRefinementLabel.admittedOnly    => StandingSide.positive

def PositiveLabel (ℓ : StandingRefinementLabel) : Prop :=
  labelSide ℓ = StandingSide.positive

/-
Status soundness: positivity of the label agrees with standing.
-/
class StatusSound
  {α : Type}
  (S : System α) : Prop where
  status_positive_iff :
    ∀ a : α,
      PositiveLabel (standing_refinement_status S a) ↔ standing S a

/-
No same-side refinement on the positive side:
every positive label collapses to standingBearing.
-/
class NoPositiveSideRefinement
  {α : Type}
  (S : System α) : Prop where
  positive_labels_collapse :
    ∀ ℓ : StandingRefinementLabel,
      PositiveLabel ℓ → ℓ = StandingRefinementLabel.standingBearing

/-
Main theorem: admittedOnly cannot occur.
-/
theorem no_admitted_only_label_for_standing_refinement_status
  {α : Type}
  (S : System α)
  [StatusSound S]
  [NoPositiveSideRefinement S] :
  ∀ a : α,
    standing_refinement_status S a ≠ StandingRefinementLabel.admittedOnly := by
  intro a
  intro h
  have hPos : PositiveLabel (standing_refinement_status S a) := by
    rw [h]
    unfold PositiveLabel labelSide
    simp
  have hCollapse :
      standing_refinement_status S a = StandingRefinementLabel.standingBearing :=
    NoPositiveSideRefinement.positive_labels_collapse
      (S := S) _ hPos
  rw [h] at hCollapse
  cases hCollapse

end MaleyLean
