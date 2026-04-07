namespace MaleyLean

/--
Abstract mediator-side mass relation corresponding to `m_W^2 = g_2^2 v^2 / 4`.
-/
def massFromGaugeCoupling
  {G : Type}
  [Mul G] [Div G] [OfNat G 4]
  (g2sq vsq : G) : G :=
  (g2sq * vsq) / 4

/--
Abstract restricted-scope charged-current witness corresponding to
`G_F / sqrt 2 = g_2^2 / (8 m_W^2)`.
-/
def gfFromMediator
  {G : Type}
  [Mul G] [Div G] [OfNat G 8]
  (g2sq mWsq : G) : G :=
  g2sq / (8 * mWsq)

/--
Abstract VEV-side collapse target corresponding to `1 / (2 v^2)`.
-/
def gfFromVev
  {G : Type}
  [Mul G] [Div G] [OfNat G 2] [One G]
  (vsq : G) : G :=
  1 / (2 * vsq)

/--
Restricted-scope formula chain:
if the mediator-side witness is matched through the mediator mass relation, and
the resulting arithmetic collapse is supplied, then the charged-current witness
collapses to the VEV-side expression.
-/
theorem charged_current_restricted_formula_chain
  {G : Type}
  [Mul G] [Div G] [OfNat G 2] [OfNat G 4] [OfNat G 8] [One G]
  (g2sq vsq mWsq gf : G)
  (h_mW : mWsq = massFromGaugeCoupling g2sq vsq)
  (h_match : gf = gfFromMediator g2sq mWsq)
  (h_collapse :
    gfFromMediator g2sq (massFromGaugeCoupling g2sq vsq) = gfFromVev vsq) :
  gf = gfFromVev vsq := by
  rw [h_match]
  rw [h_mW]
  exact h_collapse

/--
Extended-scope dimension-6 witness channel.
-/
def c6FromGF
  {G : Type}
  (gf : G) : G :=
  gf

/--
Extended-scope dimension-8 witness channel, abstractly represented as the
dimension-6 witness multiplied by an additional inverse-mass witness.
-/
def c8FromGFAndInvMass
  {G : Type}
  [Mul G]
  (gf invMassSq : G) : G :=
  gf * invMassSq

/--
Extended-scope reconstruction:
once the restricted witness and the additional inverse-mass witness are fixed,
the pair of effective coefficients is fixed as well.
-/
theorem charged_current_extended_witness_reconstruction
  {G : Type}
  [Mul G]
  (gf invMassSq : G) :
  (c6FromGF gf, c8FromGFAndInvMass gf invMassSq) =
    (gf, gf * invMassSq) := by
  rfl

end MaleyLean
