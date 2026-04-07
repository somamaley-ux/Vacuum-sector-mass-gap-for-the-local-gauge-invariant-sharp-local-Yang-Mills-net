import MaleyLean.HyperchargeQuantization

namespace MaleyLean

/--
Paper-facing support statement for
"Hypercharge Normalization and Electric Charge Quantization under Admissible
Redescription".

This is the minimal faithful Lean surface for the current repo: it certifies the
equivalence logic and the no-split consequence without pretending that the full
hypercharge-assignment algebra has already been formalized here.
-/
theorem PaperHyperchargeChargeQuantizationEquivalenceStatement
  {C : Type}
  (D : HyperchargeQuantizationData C)
  (h_toQuantized :
    ∀ c : C, D.normalized c → D.chargeQuantized c)
  (h_toNormalized :
    ∀ c : C, D.chargeQuantized c → D.normalized c) :
  ∀ c : C, D.normalized c ↔ D.chargeQuantized c := by
  exact
    normalization_iff_charge_quantized
      D
      h_toQuantized
      h_toNormalized

theorem PaperNoHyperchargeQuantizationSplitStatement
  {C : Type}
  (D : HyperchargeQuantizationData C)
  (h_toQuantized :
    ∀ c : C, D.normalized c → D.chargeQuantized c)
  (h_toNormalized :
    ∀ c : C, D.chargeQuantized c → D.normalized c) :
  ¬ normalization_quantization_split D := by
  exact
    no_normalization_quantization_split
      D
      h_toQuantized
      h_toNormalized

end MaleyLean
