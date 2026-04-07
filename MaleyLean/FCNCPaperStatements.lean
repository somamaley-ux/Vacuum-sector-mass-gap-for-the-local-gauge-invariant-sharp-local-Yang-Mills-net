import MaleyLean.FCNCEquivalence

namespace MaleyLean

/--
Paper-facing support statement for
"Higgs Alignment iff Absence of Tree-Level Flavor-Changing Neutral Currents".

This is the minimal faithful Lean surface for the current repo: it certifies the
equivalence logic and the no-split consequence without pretending that the full
Higgs/flavor alignment algebra has already been formalized here.
-/
theorem PaperHiggsAlignmentFCNCEquivalenceStatement
  {C : Type}
  (D : FCNCEquivalenceData C)
  (h_toFCNC :
    ∀ c : C, D.aligned c → D.noTreeLevelFCNC c)
  (h_toAlign :
    ∀ c : C, D.noTreeLevelFCNC c → D.aligned c) :
  ∀ c : C, D.aligned c ↔ D.noTreeLevelFCNC c := by
  exact
    alignment_iff_no_tree_level_fcnc
      D
      h_toFCNC
      h_toAlign

theorem PaperNoAlignmentFCNCSplitStatement
  {C : Type}
  (D : FCNCEquivalenceData C)
  (h_toFCNC :
    ∀ c : C, D.aligned c → D.noTreeLevelFCNC c)
  (h_toAlign :
    ∀ c : C, D.noTreeLevelFCNC c → D.aligned c) :
  ¬ alignment_fcnc_split D := by
  exact
    no_alignment_fcnc_split
      D
      h_toFCNC
      h_toAlign

end MaleyLean
