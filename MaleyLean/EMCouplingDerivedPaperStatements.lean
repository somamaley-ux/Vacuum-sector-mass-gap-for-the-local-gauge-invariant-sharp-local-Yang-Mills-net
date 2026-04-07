import MaleyLean.EMCouplingPaperStatements
import MaleyLean.EMCouplingDerived

namespace MaleyLean

/--
Derived paper-facing shared-witness statement for the EM coupling paper.

This strengthens the first-pass support surface by recording that electroweak-
side and electromagnetic-side bookkeeping collapse to a common canonical
witness channel.
-/
theorem PaperEMCouplingSharedWitnessStatement
  {C W : Type}
  (D : EMCouplingWitnessData C W)
  (h_ew :
    ∀ c : C, D.ewWitness c = D.witness c)
  (h_em :
    ∀ c : C, D.emWitness c = D.witness c) :
  ∀ c : C, D.ewWitness c = D.emWitness c := by
  exact
    ew_and_em_share_witness
      D
      h_ew
      h_em

theorem PaperNoEMCouplingWitnessSplitStatement
  {C W : Type}
  (D : EMCouplingWitnessData C W)
  (h_ew :
    ∀ c : C, D.ewWitness c = D.witness c)
  (h_em :
    ∀ c : C, D.emWitness c = D.witness c) :
  ¬ ∃ c : C, D.ewWitness c ≠ D.emWitness c := by
  exact
    no_ew_em_witness_split
      D
      h_ew
      h_em

end MaleyLean
