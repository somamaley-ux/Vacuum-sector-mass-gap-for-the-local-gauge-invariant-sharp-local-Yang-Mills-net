import MaleyLean.ChargedCurrentPaperStatements
import MaleyLean.ChargedCurrentDerived

namespace MaleyLean

/--
Derived paper-facing formula chain for the restricted charged-current collapse.

This strengthens the first-pass support surface by recording an explicit
mediator-to-VEV witness collapse chain, still without claiming a full electroweak
EFT derivation inside Lean.
-/
theorem PaperChargedCurrentRestrictedFormulaChainStatement
  {G : Type}
  [Mul G] [Div G] [OfNat G 2] [OfNat G 4] [OfNat G 8] [One G]
  (g2sq vsq mWsq gf : G)
  (h_mW : mWsq = massFromGaugeCoupling g2sq vsq)
  (h_match : gf = gfFromMediator g2sq mWsq)
  (h_collapse :
    gfFromMediator g2sq (massFromGaugeCoupling g2sq vsq) = gfFromVev vsq) :
  gf = gfFromVev vsq := by
  exact
    charged_current_restricted_formula_chain
      g2sq
      vsq
      mWsq
      gf
      h_mW
      h_match
      h_collapse

/--
Derived paper-facing statement for the enlarged-scope witness pair.
-/
theorem PaperChargedCurrentExtendedWitnessReconstructionStatement
  {G : Type}
  [Mul G]
  (gf invMassSq : G) :
  (c6FromGF gf, c8FromGFAndInvMass gf invMassSq) =
    (gf, gf * invMassSq) := by
  exact
    charged_current_extended_witness_reconstruction
      gf
      invMassSq

end MaleyLean
