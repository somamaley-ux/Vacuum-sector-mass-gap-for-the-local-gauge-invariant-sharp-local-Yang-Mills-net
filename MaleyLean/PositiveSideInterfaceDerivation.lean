import MaleyLean.PositiveSideEffectiveness
import MaleyLean.BivalenceInterface

namespace MaleyLean

theorem admitted_side_good_all
  (u : StandingRefinementLabel) :
  admitted_side_good u := by
  cases u <;> trivial

theorem no_effective_split_on_admitted_side
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) :
  ¬ effective_split
      RefStatus
      admitted_side_good
      scope_preserving
      StandingRefinementLabel.admittedOnly
      StandingRefinementLabel.standingBearing := by
  intro h
  rcases h with ⟨a, b, C, _ha, _hb, _hscope, hdisc⟩
  rcases hdisc with hleft | hright
  · exact hleft.2 (admitted_side_good_all _)
  · exact hright.2 (admitted_side_good_all _)

theorem inert_split_on_admitted_side
  {α : Type}
  (rel : α → α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_bin :
    binary_admissibility_interface
      rel
      RefStatus
      admitted_side_good
      scope_preserving) :
  inert_split
    rel
    RefStatus
    admitted_side_good
    scope_preserving
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing := by
  exact
    h_bin
      StandingRefinementLabel.admittedOnly
      StandingRefinementLabel.standingBearing
      standing_refinement_labels_same_side_on_admitted_side

theorem no_effective_split_on_admitted_side_of_bivalence
  {α : Type}
  (rel : α → α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_bin :
    binary_admissibility_interface
      rel
      RefStatus
      admitted_side_good
      scope_preserving) :
  ¬ effective_split
      RefStatus
      admitted_side_good
      scope_preserving
      StandingRefinementLabel.admittedOnly
      StandingRefinementLabel.standingBearing := by
  exact
    inert_split_not_effective
      rel
      RefStatus
      admitted_side_good
      scope_preserving
      StandingRefinementLabel.admittedOnly
      StandingRefinementLabel.standingBearing
      (inert_split_on_admitted_side
        rel
        RefStatus
        scope_preserving
        h_bin)

def positive_side_effectiveness_bridge
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  effective_positive_side_refinement
    Admitted
    RefStatus
    scope_preserving →
  effective_split
    RefStatus
    admitted_side_good
    scope_preserving
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing

theorem binary_positive_side_effectiveness_interface_of_bivalence_and_bridge
  {α : Type}
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_bin :
    binary_admissibility_interface
      rel
      RefStatus
      admitted_side_good
      scope_preserving)
  (h_bridge :
    positive_side_effectiveness_bridge
      Admitted
      RefStatus
      scope_preserving) :
  binary_positive_side_effectiveness_interface
    Admitted
    RefStatus
    scope_preserving := by
  intro h_eff
  have h_eff_old :
      effective_split
        RefStatus
        admitted_side_good
        scope_preserving
        StandingRefinementLabel.admittedOnly
        StandingRefinementLabel.standingBearing := by
    exact h_bridge h_eff
  exact
    (no_effective_split_on_admitted_side_of_bivalence
      rel
      RefStatus
      scope_preserving
      h_bin)
      h_eff_old

theorem substantive_positive_refinement_forbidden_of_bivalence_and_bridge
  {α : Type}
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_adm :
    ∀ a : α,
      standing S a →
      Admitted a)
  (h_status_admitted_only :
    ∀ a : α,
      admitted_only S Admitted a →
      RefStatus a = StandingRefinementLabel.admittedOnly)
  (h_status_standing :
    ∀ a : α,
      standing S a →
      RefStatus a = StandingRefinementLabel.standingBearing)
  (h_bin :
    binary_admissibility_interface
      rel
      RefStatus
      admitted_side_good
      scope_preserving)
  (h_bridge :
    positive_side_effectiveness_bridge
      Admitted
      RefStatus
      scope_preserving) :
  ¬ substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving := by
  exact
    substantive_positive_refinement_forbidden_of_positive_side_interface
      S
      Admitted
      RefStatus
      scope_preserving
      h_adm
      h_status_admitted_only
      h_status_standing
      (binary_positive_side_effectiveness_interface_of_bivalence_and_bridge
        rel
        Admitted
        RefStatus
        scope_preserving
        h_bin
        h_bridge)

theorem no_admitted_only_of_bivalence_and_bridge
  {α : Type}
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_adm :
    ∀ a : α,
      standing S a →
      Admitted a)
  (h_substantive_if_admitted_only :
    ∀ a : α,
      admitted_only S Admitted a →
      substantive_positive_refinement
        S
        Admitted
        (standing_refinement_status S)
        scope_preserving)
  (h_bin :
    binary_admissibility_interface
      rel
      (standing_refinement_status S)
      admitted_side_good
      scope_preserving)
  (h_bridge :
    positive_side_effectiveness_bridge
      Admitted
      (standing_refinement_status S)
      scope_preserving) :
  ∀ a : α,
    admitted_only S Admitted a →
    False := by
  intro a ha
  have h_sub :
      substantive_positive_refinement
        S
        Admitted
        (standing_refinement_status S)
        scope_preserving := by
    exact h_substantive_if_admitted_only a ha
  exact
    substantive_positive_refinement_forbidden_of_bivalence_and_bridge
      S
      rel
      Admitted
      (standing_refinement_status S)
      scope_preserving
      h_adm
      (standing_refinement_status_of_admitted_only S Admitted)
      (standing_refinement_status_of_standing S)
      h_bin
      h_bridge
      h_sub

end MaleyLean
