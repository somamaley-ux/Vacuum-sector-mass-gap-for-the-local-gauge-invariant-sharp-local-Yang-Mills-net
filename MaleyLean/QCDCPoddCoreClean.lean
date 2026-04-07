namespace MaleyLean

structure CPoddPhaseOpsClean (G : Type) where
  zero : G
  add : G → G → G
  neg : G → G
  add_assoc : ∀ a b c : G, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : G, add a b = add b a
  zero_add : ∀ a : G, add zero a = a
  add_zero : ∀ a : G, add a zero = a
  add_left_neg : ∀ a : G, add (neg a) a = zero

def cpoddSubClean
  {G : Type}
  (ops : CPoddPhaseOpsClean G)
  (a b : G) : G :=
  ops.add a (ops.neg b)

def barThetaClean
  {G : Type}
  (ops : CPoddPhaseOpsClean G)
  (theta argdetM : G) : G :=
  ops.add theta argdetM

def thetaAfterRephasingClean
  {G : Type}
  (ops : CPoddPhaseOpsClean G)
  (delta theta : G) : G :=
  ops.add theta delta

def argdetAfterRephasingClean
  {G : Type}
  (ops : CPoddPhaseOpsClean G)
  (delta argdetM : G) : G :=
  cpoddSubClean ops argdetM delta

theorem barThetaClean_invariant_under_opposite_rephasing_shifts
  {G : Type}
  (ops : CPoddPhaseOpsClean G)
  (delta theta argdetM : G) :
  barThetaClean
      ops
      (thetaAfterRephasingClean ops delta theta)
      (argdetAfterRephasingClean ops delta argdetM)
    =
      barThetaClean ops theta argdetM := by
  unfold barThetaClean thetaAfterRephasingClean argdetAfterRephasingClean cpoddSubClean
  have hcancel : ops.add delta (ops.neg delta) = ops.zero := by
    rw [ops.add_comm delta (ops.neg delta)]
    exact ops.add_left_neg delta
  have hinner : ops.add delta (ops.add argdetM (ops.neg delta)) = argdetM := by
    rw [ops.add_comm argdetM (ops.neg delta)]
    rw [← ops.add_assoc delta (ops.neg delta) argdetM]
    rw [hcancel]
    exact ops.zero_add argdetM
  rw [ops.add_assoc]
  rw [hinner]

structure QCDCPoddDataClean (UV W : Type) where
  thetaWitness : UV → W
  massPhaseWitness : UV → W
  cpOddWitness : UV → W

theorem cpodd_collapse_to_single_witness_clean
  {UV W : Type}
  (D : QCDCPoddDataClean UV W)
  (P : UV → Prop)
  (h_complete :
    ∀ u₁ u₂ : UV,
      D.cpOddWitness u₁ = D.cpOddWitness u₂ →
      (P u₁ ↔ P u₂)) :
  ∀ u₁ u₂ : UV,
    D.cpOddWitness u₁ = D.cpOddWitness u₂ →
    (P u₁ ↔ P u₂) := by
  exact h_complete

theorem no_cpodd_observable_split_clean
  {UV W : Type}
  (D : QCDCPoddDataClean UV W)
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
