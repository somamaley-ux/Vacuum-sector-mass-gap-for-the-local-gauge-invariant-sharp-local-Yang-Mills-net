namespace MaleyLean

/--
Minimal domain skeleton for the support paper
"Hypercharge Normalization and Electric Charge Quantization under Admissible
Redescription".

`C` is the bookkeeping type for the fixed chiral load and Higgs structure. The
two predicates represent the two allegedly independent constraint surfaces:
- admissible hypercharge normalization (up to the allowed sign convention)
- electric charge quantization in the broken-phase skin
-/
structure HyperchargeQuantizationData (C : Type) where
  normalized : C → Prop
  chargeQuantized : C → Prop

/--
An apparent normalization/quantization split would mean that some bookkeeping
choice admits one of the two constraints without the other.
-/
def normalization_quantization_split
  {C : Type}
  (D : HyperchargeQuantizationData C) : Prop :=
  ∃ c : C,
    (D.normalized c ∧ ¬ D.chargeQuantized c) ∨
    (D.chargeQuantized c ∧ ¬ D.normalized c)

/--
Core eliminative theorem: once transport identifies the two constraint surfaces,
hypercharge normalization and electric charge quantization are equivalent
requirements.
-/
theorem normalization_iff_charge_quantized
  {C : Type}
  (D : HyperchargeQuantizationData C)
  (h_toQuantized :
    ∀ c : C, D.normalized c → D.chargeQuantized c)
  (h_toNormalized :
    ∀ c : C, D.chargeQuantized c → D.normalized c) :
  ∀ c : C, D.normalized c ↔ D.chargeQuantized c := by
  intro c
  constructor
  · exact h_toQuantized c
  · exact h_toNormalized c

/--
Failure-of-independence consequence:
if normalization and quantization are equivalent, then the fixed bookkeeping
choice admits no admissible split between them.
-/
theorem no_normalization_quantization_split
  {C : Type}
  (D : HyperchargeQuantizationData C)
  (h_toQuantized :
    ∀ c : C, D.normalized c → D.chargeQuantized c)
  (h_toNormalized :
    ∀ c : C, D.chargeQuantized c → D.normalized c) :
  ¬ normalization_quantization_split D := by
  intro hSplit
  rcases hSplit with ⟨c, hCase⟩
  rcases hCase with hLeft | hRight
  · exact hLeft.2 (h_toQuantized c hLeft.1)
  · exact hRight.2 (h_toNormalized c hRight.1)

end MaleyLean
