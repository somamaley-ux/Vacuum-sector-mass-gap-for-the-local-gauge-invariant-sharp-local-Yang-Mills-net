import MaleyLean.NeutrinoMixingPaperStatements
import MaleyLean.NeutrinoMixingDerived

namespace MaleyLean

/--
Derived paper-facing shared witness-pair statement for the neutrino paper.

This strengthens the first-pass support surface by recording that source-side
oscillation bookkeeping collapses to a canonical mass/mixing witness pair.
-/
theorem PaperNeutrinoSharedWitnessPairStatement
  {C M R : Type}
  (D : NeutrinoWitnessPairData C M R)
  (h_mass :
    ∀ c : C, D.sourceMass c = D.witnessMass c)
  (h_mix :
    ∀ c : C, D.sourceMix c = D.witnessMix c) :
  ∀ c : C,
    (D.sourceMass c, D.sourceMix c) =
      (D.witnessMass c, D.witnessMix c) := by
  exact
    neutrino_source_pair_matches_witness_pair
      D
      h_mass
      h_mix

theorem PaperNoNeutrinoWitnessPairSplitStatement
  {C M R : Type}
  (D : NeutrinoWitnessPairData C M R)
  (h_mass :
    ∀ c : C, D.sourceMass c = D.witnessMass c)
  (h_mix :
    ∀ c : C, D.sourceMix c = D.witnessMix c) :
  ¬ ∃ c : C,
      (D.sourceMass c, D.sourceMix c) ≠
        (D.witnessMass c, D.witnessMix c) := by
  exact
    no_neutrino_witness_pair_split
      D
      h_mass
      h_mix

end MaleyLean
