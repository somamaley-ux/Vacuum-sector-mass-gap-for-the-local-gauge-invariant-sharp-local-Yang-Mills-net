namespace MaleyLean

/--
Minimal domain skeleton for the support paper
"Anomaly Freedom iff Yukawa Realizability under Minimal Chiral Load".

`C` is the bookkeeping type for the fixed declared load. The two predicates are
the paper's two allegedly independent constraint surfaces:
- anomaly freedom in the chiral-gauge skin
- complete Yukawa realizability in the broken-phase skin
-/
structure AnomalyYukawaData (C : Type) where
  anomalyFree : C → Prop
  yukawaRealizable : C → Prop

/--
An apparent anomaly/Yukawa split would mean that the fixed bookkeeping choice
admits one of the two requirements without the other.
-/
def anomaly_yukawa_split
  {C : Type}
  (D : AnomalyYukawaData C) : Prop :=
  ∃ c : C,
    (D.anomalyFree c ∧ ¬ D.yukawaRealizable c) ∨
    (D.yukawaRealizable c ∧ ¬ D.anomalyFree c)

/--
Core eliminative theorem: once transport identifies the two constraint surfaces,
anomaly freedom and complete Yukawa realizability are equivalent requirements.
-/
theorem anomaly_freedom_iff_yukawa_realizability
  {C : Type}
  (D : AnomalyYukawaData C)
  (h_toYukawa :
    ∀ c : C, D.anomalyFree c → D.yukawaRealizable c)
  (h_toAnomaly :
    ∀ c : C, D.yukawaRealizable c → D.anomalyFree c) :
  ∀ c : C, D.anomalyFree c ↔ D.yukawaRealizable c := by
  intro c
  constructor
  · exact h_toYukawa c
  · exact h_toAnomaly c

/--
Failure-of-independence consequence:
if anomaly freedom and complete Yukawa realizability are equivalent, then the
fixed declared load admits no bookkeeping choice that splits them.
-/
theorem no_anomaly_yukawa_split
  {C : Type}
  (D : AnomalyYukawaData C)
  (h_toYukawa :
    ∀ c : C, D.anomalyFree c → D.yukawaRealizable c)
  (h_toAnomaly :
    ∀ c : C, D.yukawaRealizable c → D.anomalyFree c) :
  ¬ anomaly_yukawa_split D := by
  intro hSplit
  rcases hSplit with ⟨c, hCase⟩
  rcases hCase with hLeft | hRight
  · exact hLeft.2 (h_toYukawa c hLeft.1)
  · exact hRight.2 (h_toAnomaly c hRight.1)

end MaleyLean
