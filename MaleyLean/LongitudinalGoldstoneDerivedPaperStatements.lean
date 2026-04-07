import MaleyLean.LongitudinalGoldstonePaperStatements
import MaleyLean.LongitudinalGoldstoneDerived

namespace MaleyLean

/--
Derived paper-facing shared-witness statement for the longitudinal/Goldstone
paper.

This strengthens the first-pass support surface by recording that longitudinal-
side and Goldstone-side bookkeeping collapse to a common canonical witness
channel.
-/
theorem PaperLongitudinalGoldstoneSharedWitnessStatement
  {C W : Type}
  (D : LongitudinalGoldstoneWitnessData C W)
  (h_longitudinal :
    ∀ c : C, D.longitudinalWitness c = D.witness c)
  (h_goldstone :
    ∀ c : C, D.goldstoneWitness c = D.witness c) :
  ∀ c : C, D.longitudinalWitness c = D.goldstoneWitness c := by
  exact
    longitudinal_and_goldstone_share_witness
      D
      h_longitudinal
      h_goldstone

theorem PaperNoLongitudinalGoldstoneWitnessSplitStatement
  {C W : Type}
  (D : LongitudinalGoldstoneWitnessData C W)
  (h_longitudinal :
    ∀ c : C, D.longitudinalWitness c = D.witness c)
  (h_goldstone :
    ∀ c : C, D.goldstoneWitness c = D.witness c) :
  ¬ ∃ c : C, D.longitudinalWitness c ≠ D.goldstoneWitness c := by
  exact
    no_longitudinal_goldstone_witness_split
      D
      h_longitudinal
      h_goldstone

end MaleyLean
