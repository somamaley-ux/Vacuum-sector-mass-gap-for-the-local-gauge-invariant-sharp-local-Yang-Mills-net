namespace MaleyLean

/--
Minimal derived witness layer for the neutrino-mixing paper.

`C` is the bookkeeping type. `M` tracks the mass-difference channel and `R`
tracks the rephasing-invariant mixing channel. This layer records the stronger
derivation shape where both sides collapse to the same canonical witness pair.
-/
structure NeutrinoWitnessPairData (C M R : Type) where
  witnessMass : C → M
  witnessMix : C → R
  sourceMass : C → M
  sourceMix : C → R

/--
If the source-side oscillation bookkeeping is read off the same canonical mass
and mixing witness pair, then the source pair agrees with the canonical pair
pointwise.
-/
theorem neutrino_source_pair_matches_witness_pair
  {C M R : Type}
  (D : NeutrinoWitnessPairData C M R)
  (h_mass :
    ∀ c : C, D.sourceMass c = D.witnessMass c)
  (h_mix :
    ∀ c : C, D.sourceMix c = D.witnessMix c) :
  ∀ c : C,
    (D.sourceMass c, D.sourceMix c) =
      (D.witnessMass c, D.witnessMix c) := by
  intro c
  exact Prod.ext (h_mass c) (h_mix c)

/--
Derived no-split consequence at the witness-pair layer.
-/
theorem no_neutrino_witness_pair_split
  {C M R : Type}
  (D : NeutrinoWitnessPairData C M R)
  (h_mass :
    ∀ c : C, D.sourceMass c = D.witnessMass c)
  (h_mix :
    ∀ c : C, D.sourceMix c = D.witnessMix c) :
  ¬ ∃ c : C,
      (D.sourceMass c, D.sourceMix c) ≠
        (D.witnessMass c, D.witnessMix c) := by
  intro hSplit
  rcases hSplit with ⟨c, hNe⟩
  exact hNe (neutrino_source_pair_matches_witness_pair D h_mass h_mix c)

end MaleyLean
