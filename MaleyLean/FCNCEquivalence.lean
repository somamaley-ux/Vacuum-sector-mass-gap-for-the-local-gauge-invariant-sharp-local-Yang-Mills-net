namespace MaleyLean

/--
Minimal domain skeleton for the support paper
"Higgs Alignment iff Absence of Tree-Level Flavor-Changing Neutral Currents".

`C` is the bookkeeping type for the fixed electroweak/Higgs-fermion load. The
two predicates represent the two allegedly independent constraint surfaces:
- admissible Higgs/fermion alignment in the unbroken skin
- absence of tree-level FCNCs in the broken-phase skin
-/
structure FCNCEquivalenceData (C : Type) where
  aligned : C → Prop
  noTreeLevelFCNC : C → Prop

/--
An apparent alignment/FCNC split would mean that some bookkeeping choice admits
one of the two constraints without the other.
-/
def alignment_fcnc_split
  {C : Type}
  (D : FCNCEquivalenceData C) : Prop :=
  ∃ c : C,
    (D.aligned c ∧ ¬ D.noTreeLevelFCNC c) ∨
    (D.noTreeLevelFCNC c ∧ ¬ D.aligned c)

/--
Core eliminative theorem: once transport identifies the two constraint surfaces,
alignment and tree-level FCNC absence are equivalent requirements.
-/
theorem alignment_iff_no_tree_level_fcnc
  {C : Type}
  (D : FCNCEquivalenceData C)
  (h_toFCNC :
    ∀ c : C, D.aligned c → D.noTreeLevelFCNC c)
  (h_toAlign :
    ∀ c : C, D.noTreeLevelFCNC c → D.aligned c) :
  ∀ c : C, D.aligned c ↔ D.noTreeLevelFCNC c := by
  intro c
  constructor
  · exact h_toFCNC c
  · exact h_toAlign c

/--
Failure-of-independence consequence:
if alignment and FCNC absence are equivalent, then the fixed bookkeeping choice
admits no admissible alignment/FCNC split.
-/
theorem no_alignment_fcnc_split
  {C : Type}
  (D : FCNCEquivalenceData C)
  (h_toFCNC :
    ∀ c : C, D.aligned c → D.noTreeLevelFCNC c)
  (h_toAlign :
    ∀ c : C, D.noTreeLevelFCNC c → D.aligned c) :
  ¬ alignment_fcnc_split D := by
  intro hSplit
  rcases hSplit with ⟨c, hCase⟩
  rcases hCase with hLeft | hRight
  · exact hLeft.2 (h_toFCNC c hLeft.1)
  · exact hRight.2 (h_toAlign c hRight.1)

end MaleyLean
