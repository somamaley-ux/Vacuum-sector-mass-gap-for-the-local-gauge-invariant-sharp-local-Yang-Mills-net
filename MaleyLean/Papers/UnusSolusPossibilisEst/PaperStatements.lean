import MaleyLean.Papers.UnusSolusPossibilisEst.ManuscriptTheorems

namespace MaleyLean
namespace Papers
namespace UnusSolusPossibilisEst

/--
Compatibility shim for older imports.

The canonical paper encoding now lives in `ManuscriptTheorems.lean`.
This file re-exports the paper-facing names most older callers would expect.
-/

abbrev standingValue
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (D : Domain)
    (a : Act) : Prop :=
  StandingOne S D a

abbrev uniqueAdmissibleInterior
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  UniqueAdmissibleInterior S

abbrev noRepairsForEvaluatedActs
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  NoRepairsForEvaluatedActs S

abbrev transferWithoutStanding
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  TransferWithoutStanding S

abbrev referenceFixationNecessary
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain) : Prop :=
  ReferenceFixationNecessary S

theorem PaperUniquenessOfAdmissibleInteriorStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_unique : uniqueAdmissibleInterior S) :
    uniqueAdmissibleInterior S := by
  exact PaperUniquenessOfTheAdmissibleInteriorStatement S h_unique

theorem PaperNoRepairsForEvaluatedActsStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_noRepairs : noRepairsForEvaluatedActs S) :
    noRepairsForEvaluatedActs S := by
  exact PaperNoRepairsForAnEvaluatedActStatement S h_noRepairs

theorem PaperReferenceFixationNecessaryForTheoryLevelConfirmationStatement
    {Act Domain : Type}
    (S : ApexClosureSystem Act Domain)
    (h_fixation : referenceFixationNecessary S) :
    referenceFixationNecessary S := by
  exact
    Papers.UnusSolusPossibilisEst.PaperReferenceFixationIsNecessaryForTheoryLevelConfirmationStatement
      S
      h_fixation

end UnusSolusPossibilisEst
end Papers
end MaleyLean
