import MaleyLean.YukawaMassPaperStatements
import MaleyLean.YukawaMassDerived

namespace MaleyLean

/--
Derived paper-facing shared-witness statement for the Yukawa/mass paper.

This strengthens the first-pass support surface by recording that mass-side and
Yukawa-side bookkeeping collapse to a common canonical witness channel.
-/
theorem PaperYukawaMassSharedWitnessStatement
  {C W : Type}
  (D : YukawaMassWitnessData C W)
  (h_mass :
    ∀ c : C, D.massWitness c = D.witness c)
  (h_yukawa :
    ∀ c : C, D.yukawaWitness c = D.witness c) :
  ∀ c : C, D.massWitness c = D.yukawaWitness c := by
  exact
    mass_and_yukawa_share_witness
      D
      h_mass
      h_yukawa

theorem PaperNoYukawaMassWitnessSplitStatement
  {C W : Type}
  (D : YukawaMassWitnessData C W)
  (h_mass :
    ∀ c : C, D.massWitness c = D.witness c)
  (h_yukawa :
    ∀ c : C, D.yukawaWitness c = D.witness c) :
  ¬ ∃ c : C, D.massWitness c ≠ D.yukawaWitness c := by
  exact
    no_yukawa_mass_witness_split
      D
      h_mass
      h_yukawa

end MaleyLean
