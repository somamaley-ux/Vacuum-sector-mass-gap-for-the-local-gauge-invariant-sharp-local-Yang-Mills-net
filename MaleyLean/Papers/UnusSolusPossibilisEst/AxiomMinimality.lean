import MaleyLean.Papers.UnusSolusPossibilisEst.DegeneracyCases

namespace MaleyLean
namespace Papers
namespace UnusSolusPossibilisEst

inductive InternalAxiomTag where
  | intelligibility
  | irreversibility
  | composition
  | scopeDiscipline
  | miax
  | ametricBoundary
  | bivalence
deriving DecidableEq, Repr

inductive DerivedResultTag where
  | gateExistence
  | binaryStanding
  | noParameterization
  | uniqueGate
  | noRepairs
  | noGenerators
  | authorizerIsGate
  | noCarriers
  | probabilityNotPrimitive
  | explanationNotPrimitive
  | conservation
  | noScopeTransport
  | transferWithoutStanding
  | fixationNecessary
  | noDiscreteInteriors
  | uniqueness
  | apexClosure
deriving DecidableEq, Repr

def dependencyMatrix : DerivedResultTag → List InternalAxiomTag
  | .gateExistence => [ .intelligibility, .irreversibility ]
  | .binaryStanding => [ .bivalence ]
  | .noParameterization => [ .ametricBoundary ]
  | .uniqueGate => [ .intelligibility, .ametricBoundary, .bivalence ]
  | .noRepairs => [ .irreversibility ]
  | .noGenerators => [ .irreversibility ]
  | .authorizerIsGate => [ .bivalence ]
  | .noCarriers => [ .intelligibility, .miax, .ametricBoundary, .bivalence ]
  | .probabilityNotPrimitive => [ .intelligibility, .miax, .ametricBoundary, .bivalence ]
  | .explanationNotPrimitive => [ .intelligibility, .irreversibility, .miax, .ametricBoundary, .bivalence ]
  | .conservation => [ .intelligibility, .irreversibility, .miax, .ametricBoundary, .bivalence ]
  | .noScopeTransport => [ .scopeDiscipline ]
  | .transferWithoutStanding => [ .intelligibility, .scopeDiscipline, .miax, .ametricBoundary, .bivalence ]
  | .fixationNecessary => [ .intelligibility, .miax, .ametricBoundary, .bivalence ]
  | .noDiscreteInteriors => [ .intelligibility, .ametricBoundary, .bivalence ]
  | .uniqueness => [ .intelligibility, .ametricBoundary, .bivalence ]
  | .apexClosure => [ .intelligibility, .irreversibility, .scopeDiscipline, .miax, .ametricBoundary, .bivalence ]

abbrev minimalAxiomSet := dependencyMatrix

def axiomUsedBy (r : DerivedResultTag) (a : InternalAxiomTag) : Prop :=
  a ∈ dependencyMatrix r

theorem composition_is_nonminimal_in_standalone_derivation :
    ∀ r : DerivedResultTag, ¬ axiomUsedBy r .composition := by
  intro r
  cases r <;> simp [axiomUsedBy, dependencyMatrix]

def reopenedDegeneracyForDroppedAxiom : InternalAxiomTag → String
  | .intelligibility => "D^I_Sigma: fixation drift (D16-type)"
  | .irreversibility => "D^R_Sigma: same-act repair (D1 / no-repairs failure)"
  | .composition => "D^C_Sigma: non-composition of redescription"
  | .scopeDiscipline => "D^S_Sigma: scope legalization (D6-type)"
  | .miax => "D^M_Sigma: redescription-variant standing (D11-type)"
  | .ametricBoundary => "D^A_Sigma: threshold carrier authorizes standing (D4-type)"
  | .bivalence => "D^B_Sigma: third standing value (graded / ternary standing)"

theorem dropped_intelligibility_reopens_named_degeneracy :
    reopenedDegeneracyForDroppedAxiom .intelligibility =
      "D^I_Sigma: fixation drift (D16-type)" := by
  rfl

theorem dropped_irreversibility_reopens_named_degeneracy :
    reopenedDegeneracyForDroppedAxiom .irreversibility =
      "D^R_Sigma: same-act repair (D1 / no-repairs failure)" := by
  rfl

theorem dropped_composition_reopens_named_degeneracy :
    reopenedDegeneracyForDroppedAxiom .composition =
      "D^C_Sigma: non-composition of redescription" := by
  rfl

theorem dropped_scope_discipline_reopens_named_degeneracy :
    reopenedDegeneracyForDroppedAxiom .scopeDiscipline =
      "D^S_Sigma: scope legalization (D6-type)" := by
  rfl

theorem dropped_miax_reopens_named_degeneracy :
    reopenedDegeneracyForDroppedAxiom .miax =
      "D^M_Sigma: redescription-variant standing (D11-type)" := by
  rfl

theorem dropped_ametric_boundary_reopens_named_degeneracy :
    reopenedDegeneracyForDroppedAxiom .ametricBoundary =
      "D^A_Sigma: threshold carrier authorizes standing (D4-type)" := by
  rfl

theorem dropped_bivalence_reopens_named_degeneracy :
    reopenedDegeneracyForDroppedAxiom .bivalence =
      "D^B_Sigma: third standing value (graded / ternary standing)" := by
  rfl

end UnusSolusPossibilisEst
end Papers
end MaleyLean
