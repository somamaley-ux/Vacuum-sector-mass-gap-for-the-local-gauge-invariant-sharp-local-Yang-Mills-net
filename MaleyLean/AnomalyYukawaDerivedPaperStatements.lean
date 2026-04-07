import MaleyLean.AnomalyYukawaPaperStatements
import MaleyLean.AnomalyYukawaDerived

namespace MaleyLean

/--
Derived paper-facing shared-witness statement for the anomaly/Yukawa paper.

This strengthens the first-pass support surface by recording that anomaly-side
and Yukawa-side bookkeeping collapse to a common canonical witness channel.
-/
theorem PaperAnomalyYukawaSharedWitnessStatement
  {C W : Type}
  (D : AnomalyYukawaWitnessData C W)
  (h_anomaly :
    ∀ c : C, D.anomalyWitness c = D.witness c)
  (h_yukawa :
    ∀ c : C, D.yukawaWitness c = D.witness c) :
  ∀ c : C, D.anomalyWitness c = D.yukawaWitness c := by
  exact
    anomaly_and_yukawa_share_witness
      D
      h_anomaly
      h_yukawa

theorem PaperNoAnomalyYukawaWitnessSplitStatement
  {C W : Type}
  (D : AnomalyYukawaWitnessData C W)
  (h_anomaly :
    ∀ c : C, D.anomalyWitness c = D.witness c)
  (h_yukawa :
    ∀ c : C, D.yukawaWitness c = D.witness c) :
  ¬ ∃ c : C, D.anomalyWitness c ≠ D.yukawaWitness c := by
  exact
    no_anomaly_yukawa_witness_split
      D
      h_anomaly
      h_yukawa

end MaleyLean
