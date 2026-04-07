import MaleyLean.AnomalyYukawaEquivalence

namespace MaleyLean

/--
Paper-facing support statement for
"Anomaly Freedom iff Yukawa Realizability under Minimal Chiral Load".

This is the minimal faithful Lean surface for the current repo: it certifies the
equivalence logic and the no-split consequence without pretending that the full
Standard-Model anomaly algebra or explicit gauge-invariant Yukawa operator
construction has already been formalized here.
-/
theorem PaperAnomalyYukawaEquivalenceStatement
  {C : Type}
  (D : AnomalyYukawaData C)
  (h_toYukawa :
    ∀ c : C, D.anomalyFree c → D.yukawaRealizable c)
  (h_toAnomaly :
    ∀ c : C, D.yukawaRealizable c → D.anomalyFree c) :
  ∀ c : C, D.anomalyFree c ↔ D.yukawaRealizable c := by
  exact
    anomaly_freedom_iff_yukawa_realizability
      D
      h_toYukawa
      h_toAnomaly

theorem PaperNoAnomalyYukawaSplitStatement
  {C : Type}
  (D : AnomalyYukawaData C)
  (h_toYukawa :
    ∀ c : C, D.anomalyFree c → D.yukawaRealizable c)
  (h_toAnomaly :
    ∀ c : C, D.yukawaRealizable c → D.anomalyFree c) :
  ¬ anomaly_yukawa_split D := by
  exact
    no_anomaly_yukawa_split
      D
      h_toYukawa
      h_toAnomaly

end MaleyLean
