import MaleyLean.FCNCPaperStatements
import MaleyLean.FCNCDerived

namespace MaleyLean

/--
Derived paper-facing shared-witness statement for the FCNC paper.

This strengthens the first-pass support surface by recording that alignment-side
and FCNC-side bookkeeping collapse to a common canonical witness channel.
-/
theorem PaperFCNCSharedWitnessStatement
  {C W : Type}
  (D : FCNCWitnessData C W)
  (h_align :
    ∀ c : C, D.alignmentWitness c = D.witness c)
  (h_fcnc :
    ∀ c : C, D.fcncWitness c = D.witness c) :
  ∀ c : C, D.alignmentWitness c = D.fcncWitness c := by
  exact
    alignment_and_fcnc_share_witness
      D
      h_align
      h_fcnc

theorem PaperNoFCNCWitnessSplitStatement
  {C W : Type}
  (D : FCNCWitnessData C W)
  (h_align :
    ∀ c : C, D.alignmentWitness c = D.witness c)
  (h_fcnc :
    ∀ c : C, D.fcncWitness c = D.witness c) :
  ¬ ∃ c : C, D.alignmentWitness c ≠ D.fcncWitness c := by
  exact
    no_fcnc_witness_split
      D
      h_align
      h_fcnc

end MaleyLean
