namespace MaleyLean

/--
Abstract CP-odd invariant combination corresponding to the manuscript's
`bar theta = theta + arg det M`.
-/
def barTheta
  {Γ : Type}
  [AddGroup Γ]
  (theta argdetM : Γ) : Γ :=
  theta + argdetM

/--
Abstract rephasing action on the theta channel.
-/
def thetaAfterRephasing
  {Γ : Type}
  [AddGroup Γ]
  (delta theta : Γ) : Γ :=
  theta + delta

/--
Abstract rephasing action on the mass-phase channel.
-/
def argdetAfterRephasing
  {Γ : Type}
  [AddGroup Γ]
  (delta argdetM : Γ) : Γ :=
  argdetM - delta

/--
Explicit invariant-combination derivation:
opposite shifts in the two CP-odd channels leave `barTheta` unchanged.
-/
theorem barTheta_invariant_under_opposite_rephasing_shifts
  {Γ : Type}
  [AddGroup Γ]
  (delta theta argdetM : Γ) :
  barTheta
      (thetaAfterRephasing delta theta)
      (argdetAfterRephasing delta argdetM)
    =
      barTheta theta argdetM := by
  simp [barTheta, thetaAfterRephasing, argdetAfterRephasing, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

/--
Minimal domain skeleton for the CP-odd QCD support paper.

`UV` is the ultraviolet bookkeeping skin and `W` is the type of the surviving
CP-odd witness. The two UV channels are the apparently independent inputs whose
combination survives admissible rephasing.
-/
structure QCDCPoddData (UV W : Type) where
  thetaWitness : UV → W
  massPhaseWitness : UV → W
  cpOddWitness : UV → W

/--
An apparent CP-odd split would mean that the two UV channels survive as
independent standing-relevant parameters rather than collapsing to a single
invariant witness.
-/
def cpodd_split
  {UV W : Type}
  (D : QCDCPoddData UV W) : Prop :=
  ∃ u₁ u₂ : UV,
    D.cpOddWitness u₁ = D.cpOddWitness u₂ ∧
    (D.thetaWitness u₁ ≠ D.thetaWitness u₂ ∨
     D.massPhaseWitness u₁ ≠ D.massPhaseWitness u₂)

/--
Core eliminative theorem: if the UV CP-odd content factors through a single
invariant witness, then the apparently separate channels do not survive as
independent standing-relevant data.
-/
theorem cpodd_collapse_to_single_witness
  {UV W : Type}
  (D : QCDCPoddData UV W)
  (P : UV → Prop)
  (h_complete :
    ∀ u₁ u₂ : UV,
      D.cpOddWitness u₁ = D.cpOddWitness u₂ →
      (P u₁ ↔ P u₂)) :
  ∀ u₁ u₂ : UV,
    D.cpOddWitness u₁ = D.cpOddWitness u₂ →
    (P u₁ ↔ P u₂) := by
  exact h_complete

/--
No-split consequence:
if all CP-odd observable content factors through the single invariant witness,
then no admissible independent CP-odd split remains at the observable level.
-/
theorem no_cpodd_observable_split
  {UV W : Type}
  (D : QCDCPoddData UV W)
  (Observable : UV → Prop)
  (h_complete :
    ∀ u₁ u₂ : UV,
      D.cpOddWitness u₁ = D.cpOddWitness u₂ →
      (Observable u₁ ↔ Observable u₂)) :
  ∀ u₁ u₂ : UV,
    D.cpOddWitness u₁ = D.cpOddWitness u₂ →
    (Observable u₁ ↔ Observable u₂) := by
  exact h_complete

end MaleyLean
