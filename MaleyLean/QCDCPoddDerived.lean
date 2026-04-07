namespace MaleyLean

/--
Clean additive derivation of the invariant CP-odd combination corresponding to
`bar theta = theta + arg det M`.
-/
def barThetaDerived
  {G : Type}
  [AddGroup G]
  (theta argdetM : G) : G :=
  theta + argdetM

def thetaAfterRephasingDerived
  {G : Type}
  [AddGroup G]
  (delta theta : G) : G :=
  theta + delta

def argdetAfterRephasingDerived
  {G : Type}
  [AddGroup G]
  (delta argdetM : G) : G :=
  argdetM - delta

theorem barThetaDerived_invariant_under_opposite_rephasing_shifts
  {G : Type}
  [AddGroup G]
  (delta theta argdetM : G) :
  barThetaDerived
      (thetaAfterRephasingDerived delta theta)
      (argdetAfterRephasingDerived delta argdetM)
    =
      barThetaDerived theta argdetM := by
  simp [barThetaDerived, thetaAfterRephasingDerived, argdetAfterRephasingDerived,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end MaleyLean
