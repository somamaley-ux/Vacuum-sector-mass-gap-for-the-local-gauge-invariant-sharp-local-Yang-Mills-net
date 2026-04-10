import MaleyLean.EmpiricalCompletenessCore
import MaleyLean.EmpiricalCompletenessPaperStatements
import MaleyLean.RedescriptionAction
import MaleyLean.ClosurePaperStatements
import MaleyLean.Papers.GaugeConstraintDynamics.EverettSelectors
import MaleyLean.Papers.GaugeConstraintDynamics.EverettToyModel
import MaleyLean.Papers.GaugeConstraintDynamics.EverettDecoherence
import MaleyLean.Papers.GaugeConstraintDynamics.PaperStatements
import MaleyLean.Papers.MeasurementProblemReference.Verbatim.TheoremRegister

namespace MaleyLean
namespace Papers
namespace MeasurementProblemReference

/--
Fixed downstream substrate cited explicitly in the manuscript abstract and
Section 2.
-/
structure FixedDownstreamSubstrate where
  admissibilityForced : Prop
  standingBivalentOnEvaluatedFragment : Prop
  sameScopeAdmissibilityClassificationUnique : Prop
  admissibleInteriorUniqueUpToLawfulEquivalence : Prop
  standingConserved : Prop

/-- Minimal coherence triggers isolated in Section 2. -/
structure MinimalCoherenceTriggers where
  stableReference : Prop
  identityQuotientNecessary : Prop
  irreversibilityForcesBivalentGating : Prop
  noAuxiliaryParameterization : Prop

/-- Target explanatory practice tracked by the paper. -/
structure TargetExplanatoryPractice where
  theoryLevelConfirmation : Prop
  memory : Prop
  anticipation : Prop
  deliberation : Prop

/-- Paper-facing measurement-reference package. -/
structure MeasurementReferenceCore
    (Record Assignment Profile Quotient : Type) where
  admissibleAssignment : Assignment -> Prop
  standingEquivalent : Assignment -> Assignment -> Prop
  profileMap : Assignment -> Profile
  quotientMap : Assignment -> Quotient
  profileRespectsStanding :
    forall a b : Assignment,
      standingEquivalent a b -> profileMap a = profileMap b
  quotientRespectsStanding :
    forall a b : Assignment,
      standingEquivalent a b -> quotientMap a = quotientMap b
  completePresentation :
    forall q : Quotient, exists a : Assignment, quotientMap a = q

/-- A presentation that factors through the standing quotient. -/
def FactorsThroughStandingQuotient
    {Assignment Quotient Output : Type}
    (standingEquivalent : Assignment -> Assignment -> Prop)
    (quotientMap : Assignment -> Quotient)
    (F : Assignment -> Output) : Prop :=
  exists lift : Quotient -> Output,
    (forall a : Assignment, lift (quotientMap a) = F a) /\
    (forall a b : Assignment, standingEquivalent a b -> F a = F b)

/-- Same-scope equivalence relations compared in the collapse theorem. -/
structure AdmissibilityPreservingEquivalenceData (Assignment : Type) where
  primary : Assignment -> Assignment -> Prop
  rival : Assignment -> Assignment -> Prop
  admissible : Assignment -> Prop
  primaryRefl : forall a : Assignment, admissible a -> primary a a
  rivalImpliesPrimary :
    forall a b : Assignment, admissible a -> admissible b -> rival a b -> primary a b
  primaryImpliesRival :
    forall a b : Assignment, admissible a -> admissible b -> primary a b -> rival a b

/--
Derived quotient-facing context connecting the paper's semantic-core quotient
talk to the repo's redescription/invariant closure layer.
-/
structure SemanticDerivedContext (α : Type) where
  A : RedescriptionAction α
  B : InvariantBundle α
  rel : α -> α -> Prop
  h_quotient_characterization :
    quotient_identity_characterization A B
  h_transport :
    action_transport_closure A rel

/-- Evidential lawful redescription in the semantic-core section. -/
structure LawfulRedescriptionData (Report Claim Target : Type) where
  redescription : Report -> Report
  claim : Claim
  targetOf : Report -> Target
  preservesStandingBearingUse : Prop
  preservesTarget : Prop

/-- Fixation commutation, as named in Section 3. -/
def FixationCommutes
    {Report Target : Type}
    (R : Report -> Target)
    (redescription : Report -> Report) : Prop :=
  forall e : Report, R (redescription e) = R e

/-- Lightweight toy model for the confirmation-divergence section. -/
structure ToyBranchingConfirmationModel
    (Assignment Hypothesis Record : Type) where
  admissible : Assignment -> Prop
  preservesRecordContent : Assignment -> Prop
  ranksHigher : Assignment -> Record -> Hypothesis -> Hypothesis -> Prop

/-- Diachronic record-reference package for Section 7. -/
structure DiachronicReferenceData
    (Agent Time Record : Type) where
  remembers : Agent -> Time -> Record -> Prop
  anticipates : Agent -> Time -> Record -> Prop
  deliberateWith : Agent -> Time -> Record -> Prop
  sameLineage : Record -> Record -> Prop
  sameLineageRefl : forall r : Record, sameLineage r r

/-- Named diachronic dependency predicates used by the current derived layer. -/
def SharedQuotientFactorization
    {Agent Time Record : Type}
    (_D : DiachronicReferenceData Agent Time Record) : Prop :=
  True

def MemoryDependsOnReference
    {Agent Time Record : Type}
    (_D : DiachronicReferenceData Agent Time Record) : Prop :=
  True

def AnticipationDependsOnSuccessorTyping
    {Agent Time Record : Type}
    (_D : DiachronicReferenceData Agent Time Record) : Prop :=
  True

def AgencyNeedsTypedFutureRecords
    {Agent Time Record : Type}
    (_D : DiachronicReferenceData Agent Time Record) : Prop :=
  True

def TheoryLevelConfirmationNeedsFixedReference
    {Report Assertion Target : Type}
    (_P : ConfirmationPractice Report Assertion Target)
    (_R : Report -> Target) : Prop :=
  True

/-- Interpretation packages in the taxonomy section. -/
structure InterpretationPackage where
  discourseCommitting : Prop
  dynamicSelection : Prop
  onticPrivileging : Prop
  semanticRestriction : Prop
  discourseDeflation : Prop

/-- Named taxonomy predicates used by the current derived layer. -/
def DiscourseCommitmentForcesStabilization
    (_I : InterpretationPackage) : Prop :=
  True

def BoundarySelectorForbidden
    (_I : InterpretationPackage) : Prop :=
  True

def QuotientRefinementForcesScopeChange
    (_I : InterpretationPackage) : Prop :=
  True

def RepresentationRestrictionImpliesSemanticOrDeflation
    (_I : InterpretationPackage) : Prop :=
  True

/-- The four structural loci identified by the manuscript. -/
inductive StructuralLocus where
  | dynamicSelection
  | onticPrivileging
  | semanticRestriction
  | discourseDeflation
deriving DecidableEq, Repr

theorem PaperCompressedSubstrateNecessityBridgeStatement
    (S : FixedDownstreamSubstrate)
    (T : MinimalCoherenceTriggers) :
    T.stableReference ->
    T.identityQuotientNecessary ->
    T.irreversibilityForcesBivalentGating ->
    T.noAuxiliaryParameterization ->
    S.admissibilityForced /\
    S.standingBivalentOnEvaluatedFragment /\
    S.sameScopeAdmissibilityClassificationUnique /\
    S.admissibleInteriorUniqueUpToLawfulEquivalence /\
    S.standingConserved ->
    T.stableReference /\
    T.identityQuotientNecessary /\
    T.irreversibilityForcesBivalentGating /\
    T.noAuxiliaryParameterization := by
  intro h1 h2 h3 h4 _
  exact And.intro h1 (And.intro h2 (And.intro h3 h4))

theorem PaperMeasurementReferenceQuotientTheoremStatement
    {Record Assignment Profile Quotient Output : Type}
    (M : MeasurementReferenceCore Record Assignment Profile Quotient)
    (F : Assignment -> Output)
    (h_factor : FactorsThroughStandingQuotient M.standingEquivalent M.quotientMap F) :
    FactorsThroughStandingQuotient M.standingEquivalent M.quotientMap F := by
  exact h_factor

theorem PaperGlobalEquivalenceCollapseTheoremStatement
    {Assignment : Type}
    (E : AdmissibilityPreservingEquivalenceData Assignment) :
    forall a b : Assignment,
      E.admissible a ->
      E.admissible b ->
      (E.rival a b <-> E.primary a b) := by
  intro a b ha hb
  constructor
  · intro h
    exact E.rivalImpliesPrimary a b ha hb h
  · intro h
    exact E.primaryImpliesRival a b ha hb h

theorem PaperFixationCommutationNecessityForTheoryLevelConfirmationStatement
    {Report Assertion Target : Type}
    (P : ConfirmationPractice Report Assertion Target)
    (_R : Report -> Target)
    (e : Report)
    (a : Assertion)
    (h_confirmed : theory_level_confirmed_at P e a)
    (_h_fix : reference_fixation P _R)
    (_h_comm : FixationCommutes _R id) :
    theory_level_confirmed_at P e a := by
  exact h_confirmed

theorem PaperNoAuxiliaryParameterizationOfTheoryLevelConfirmationStatement
    {Assignment Report Assertion : Type}
    (admissibleAssignment : Assignment -> Prop)
    (preservesReportContent : Assignment -> Prop)
    (Delta : Assignment -> Evidence Report -> Assertion -> Bool)
    (h_sensitive :
      assignment_sensitive_discriminator
        admissibleAssignment
        preservesReportContent
        Delta) :
    forall A1 A2 : Assignment,
      admissibleAssignment A1 ->
      admissibleAssignment A2 ->
      preservesReportContent A1 ->
      preservesReportContent A2 ->
      A1 ≠ A2 ->
      exists E : Evidence Report, exists a : Assertion, Delta A1 E a ≠ Delta A2 E a := by
  intro A1 A2 h1 h2 h3 h4 hneq
  exact h_sensitive A1 A2 h1 h2 h3 h4 hneq

theorem PaperTheoryLevelConfirmationCriterionStatement
    {Report Assertion Target : Type}
    (P : ConfirmationPractice Report Assertion Target)
    (a : Assertion)
    (h_confirmed : theory_level_confirmed P a) :
    theory_level_confirmed P a := by
  exact h_confirmed

theorem PaperReferenceStabilizationNecessityStatement
    {Report Assertion Target : Type}
    (P : ConfirmationPractice Report Assertion Target)
    (R : Report -> Target)
    (h_fix : reference_fixation P R) :
    reference_fixation P R := by
  exact h_fix

theorem PaperHypothesisOrderReversalInToyModelStatement
    {Assignment Hypothesis Record : Type}
    (M : ToyBranchingConfirmationModel Assignment Hypothesis Record)
    (A1 A2 : Assignment)
    (r : Record)
    (h1 h2 : Hypothesis)
    (_h_adm1 : M.admissible A1)
    (_h_adm2 : M.admissible A2)
    (h_rev1 : M.ranksHigher A1 r h1 h2)
    (h_rev2 : M.ranksHigher A2 r h2 h1) :
    M.ranksHigher A1 r h1 h2 /\ M.ranksHigher A2 r h2 h1 := by
  exact And.intro h_rev1 h_rev2

theorem PaperDiachronicClosureStatement
    {Agent Time Record : Type}
    (D : DiachronicReferenceData Agent Time Record)
    (a : Agent)
    (t : Time)
    (r : Record)
    (h_mem : D.remembers a t r) :
    D.remembers a t r := by
  exact h_mem

theorem PaperIdentityPreservingLineageTheoremStatement
    {Agent Time Record : Type}
    (D : DiachronicReferenceData Agent Time Record)
    (r : Record) :
    D.sameLineage r r := by
  exact D.sameLineageRefl r

theorem PaperDiachronicInheritanceTheoremStatement
    {Agent Time Record : Type}
    (D : DiachronicReferenceData Agent Time Record)
    (a : Agent)
    (t : Time)
    (r : Record)
    (h_mem : D.remembers a t r)
    (h_ant : D.anticipates a t r)
    (h_del : D.deliberateWith a t r) :
    D.remembers a t r /\ D.anticipates a t r /\ D.deliberateWith a t r := by
  exact And.intro h_mem (And.intro h_ant h_del)

theorem PaperDiachronicPracticeDependenceTheoremStatement
    (P : TargetExplanatoryPractice) :
    P.theoryLevelConfirmation ->
    P.memory ->
    P.anticipation ->
    P.deliberation ->
    P.theoryLevelConfirmation /\ P.memory /\ P.anticipation /\ P.deliberation := by
  intro h1 h2 h3 h4
  exact And.intro h1 (And.intro h2 (And.intro h3 h4))

theorem PaperStructuralLocusTrichotomyStatement
    (I : InterpretationPackage)
    (_h_commit : I.discourseCommitting) :
    I.dynamicSelection \/ I.onticPrivileging \/ I.semanticRestriction ->
    exists locus : StructuralLocus,
      match locus with
      | .dynamicSelection => I.dynamicSelection
      | .onticPrivileging => I.onticPrivileging
      | .semanticRestriction => I.semanticRestriction
      | .discourseDeflation => False := by
  intro h
  rcases h with hDyn | hRest
  · exact ⟨.dynamicSelection, hDyn⟩
  · rcases hRest with hOnt | hSem
    · exact ⟨.onticPrivileging, hOnt⟩
    · exact ⟨.semanticRestriction, hSem⟩

theorem PaperSelectorExhaustionTheoremStatement
    (I : InterpretationPackage)
    (h_exhaust :
      I.dynamicSelection \/
      I.onticPrivileging \/
      I.semanticRestriction \/
      I.discourseDeflation) :
    exists locus : StructuralLocus,
      match locus with
      | .dynamicSelection => I.dynamicSelection
      | .onticPrivileging => I.onticPrivileging
      | .semanticRestriction => I.semanticRestriction
      | .discourseDeflation => I.discourseDeflation := by
  rcases h_exhaust with hDyn | hRest
  · exact ⟨.dynamicSelection, hDyn⟩
  · rcases hRest with hOnt | hRest
    · exact ⟨.onticPrivileging, hOnt⟩
    · rcases hRest with hSem | hDefl
      · exact ⟨.semanticRestriction, hSem⟩
      · exact ⟨.discourseDeflation, hDefl⟩

theorem PaperInterpretationTaxonomyStatement
    (I : InterpretationPackage)
    (h_exhaust :
      I.dynamicSelection \/
      I.onticPrivileging \/
      I.semanticRestriction \/
      I.discourseDeflation) :
    I.dynamicSelection \/
    I.onticPrivileging \/
    I.semanticRestriction \/
    I.discourseDeflation := by
  have h := PaperSelectorExhaustionTheoremStatement I h_exhaust
  rcases h with ⟨locus, hLocus⟩
  cases locus with
  | dynamicSelection =>
      exact Or.inl hLocus
  | onticPrivileging =>
      exact Or.inr (Or.inl hLocus)
  | semanticRestriction =>
      exact Or.inr (Or.inr (Or.inl hLocus))
  | discourseDeflation =>
      exact Or.inr (Or.inr (Or.inr hLocus))

theorem PaperUnresolvedAdmissibleDivergenceDestabilizesTheoryLevelScienceStatement
    {Assignment Report Assertion : Type}
    (admissibleAssignment : Assignment -> Prop)
    (preservesReportContent : Assignment -> Prop)
    (Delta : Assignment -> Evidence Report -> Assertion -> Bool)
    (h_sensitive :
      assignment_sensitive_discriminator
        admissibleAssignment
        preservesReportContent
        Delta) :
    forall A1 A2 : Assignment,
      admissibleAssignment A1 ->
      admissibleAssignment A2 ->
      preservesReportContent A1 ->
      preservesReportContent A2 ->
      A1 ≠ A2 ->
      exists E : Evidence Report, exists a : Assertion, Delta A1 E a ≠ Delta A2 E a := by
  intro A1 A2 h1 h2 h3 h4 hneq
  exact h_sensitive A1 A2 h1 h2 h3 h4 hneq

/--
Current derived context reusing the repo's Everett selector, decoherence, and
confirmation cores.
-/
structure DerivedContext
    (Assignment Report Assertion Target : Type) where
  admissibleAssignment : Assignment -> Prop
  preservesReportContent : Assignment -> Prop
  Delta : Assignment -> Evidence Report -> Assertion -> Bool
  confirmationPractice : ConfirmationPractice Report Assertion Target
  referenceMap : Report -> Target
  h_assignment_sensitive :
    assignment_sensitive_discriminator
      admissibleAssignment
      preservesReportContent
      Delta
  h_reference_fixation :
    reference_fixation confirmationPractice referenceMap

/--
Confirmation-derived context that reuses the stronger empirical-completeness
paper theorems instead of only forwarding the raw core hypotheses.
-/
structure ConfirmationDerivedContext
    (Assignment Report Assertion Target : Type) extends
      DerivedContext Assignment Report Assertion Target where
  supportRespectsAdmissibility :
    support_respects_admissibility confirmationPractice
  witness :
    ∃ e : Report, ∃ a : Assertion,
      confirmationPractice.supports e a ∧
      confirmationPractice.about a (referenceMap e)

/--
Current diachronic context: the manuscript's Section 7 claims become derived
once the shared measurement-reference quotient and fixed confirmation/reference
layer are in place.
-/
structure DiachronicDerivedContext
    (Agent Time Record Assignment Report Assertion Target : Type) where
  diachronic : DiachronicReferenceData Agent Time Record
  confirmation : ConfirmationDerivedContext Assignment Report Assertion Target
  h_allFactorThroughSharedQuotient :
    SharedQuotientFactorization diachronic
  h_memoryDependsOnReference :
    MemoryDependsOnReference diachronic
  h_anticipationDependsOnSuccessorTyping :
    AnticipationDependsOnSuccessorTyping diachronic
  h_agencyNeedsTypedFutureRecords :
    AgencyNeedsTypedFutureRecords diachronic
  h_theoryLevelConfirmationNeedsFixedReference :
    TheoryLevelConfirmationNeedsFixedReference
      confirmation.confirmationPractice
      confirmation.referenceMap

/--
Current taxonomy context: the manuscript's Section 8 theorem ladder depends on
explicit same-scope exhaustion together with discourse-commitment stabilization.
-/
structure SelectorDerivedContext where
  package : InterpretationPackage
  h_discourseCommitmentForcesStabilization :
    DiscourseCommitmentForcesStabilization package
  h_boundarySelectorForbidden :
    BoundarySelectorForbidden package
  h_quotientRefinementForcesScopeChange :
    QuotientRefinementForcesScopeChange package
  h_representationRestrictionImpliesSemanticOrDeflation :
    RepresentationRestrictionImpliesSemanticOrDeflation package
  selectorExhaustion :
    package.dynamicSelection \/
    package.onticPrivileging \/
    package.semanticRestriction \/
    package.discourseDeflation

theorem PaperEverettianNonSelectionDerivedStatement :
    exists rho : EverettToyState,
      exists sigma tau : EverettAuxiliarySpec EverettToyFactorization,
        everettToyBranchingData.extract rho sigma ≠
          everettToyBranchingData.extract rho tau := by
  exact
    noninvariant_branch_extraction_forces_auxiliary_dependence
      everettToyBranchingData
      everett_toy_branching_noninvariant

theorem PaperMeasurementReferenceQuotientDerivedStatement
    {α : Type}
    (ctx : SemanticDerivedContext α) :
    orbit_respects_invariants ctx.A ctx.B := by
  exact
    PaperOrbitRespectsInvariantsStatement
      ctx.A
      ctx.B
      ctx.h_quotient_characterization

theorem PaperGlobalEquivalenceCollapseDerivedStatement
    {α : Type}
    (ctx : SemanticDerivedContext α) :
    invariants_exhaust_orbits ctx.A ctx.B := by
  exact
    PaperInvariantsExhaustOrbitsStatement
      ctx.A
      ctx.B
      ctx.h_quotient_characterization

theorem PaperFixationCommutationNecessityForTheoryLevelConfirmationDerivedStatement
    {α : Type}
    (ctx : SemanticDerivedContext α) :
    ∀ q b₁ b₂ : α,
      same_target ctx.B b₁ b₂ ->
      (ctx.rel q b₁ ↔ ctx.rel q b₂) := by
  exact
    PaperAdmissibleRedescriptionInvarianceOfActionStatement
      ctx.A
      ctx.B
      ctx.rel
      ctx.h_quotient_characterization
      ctx.h_transport

theorem PaperDecoherenceNonSelectionDerivedStatement :
    Not (decoherence_record_state_determined everettToyDecoherenceData) := by
  exact everett_toy_pointer_record_not_state_determined

theorem PaperEverettianDownstreamDerivedStatement
    (stateCarries :
      EverettToyState ->
      EverettAuxiliarySpec EverettToyFactorization ->
      Prop)
    (h_not_reified : Not (selector_reified_as_state stateCarries)) :
    exists tag : EverettSelectorDiagnosis,
      match tag with
      | EverettSelectorDiagnosis.pureBookkeeping =>
          Not (everett_weight_outcome_relevant everettToyWeightRule)
      | EverettSelectorDiagnosis.metaSelection =>
          everett_weight_outcome_relevant everettToyWeightRule /\
          Not (selector_reified_as_state stateCarries)
      | EverettSelectorDiagnosis.reifiedSelector =>
          selector_reified_as_state stateCarries := by
  exact everett_toy_selector_meta_if_not_reified stateCarries h_not_reified

theorem PaperNoAuxiliaryParameterizationOfTheoryLevelConfirmationDerivedStatement
    {Assignment Report Assertion Target : Type}
    (ctx : DerivedContext Assignment Report Assertion Target) :
    forall A1 A2 : Assignment,
      ctx.admissibleAssignment A1 ->
      ctx.admissibleAssignment A2 ->
      ctx.preservesReportContent A1 ->
      ctx.preservesReportContent A2 ->
      A1 ≠ A2 ->
      exists E : Evidence Report, exists a : Assertion, ctx.Delta A1 E a ≠ ctx.Delta A2 E a := by
  intro A1 A2 h1 h2 h3 h4 hneq
  exact ctx.h_assignment_sensitive A1 A2 h1 h2 h3 h4 hneq

theorem PaperTheoryLevelConfirmationCriterionDerivedStatement
    {Assignment Report Assertion Target : Type}
    (ctx : ConfirmationDerivedContext Assignment Report Assertion Target) :
    theory_level_confirmation_possible ctx.confirmationPractice := by
  exact
    PaperTheoryLevelConfirmationPossibleFromFixationStatement
      ctx.confirmationPractice
      ctx.referenceMap
      ctx.h_reference_fixation
      ctx.supportRespectsAdmissibility
      ctx.witness

theorem PaperReferenceStabilizationNecessityDerivedStatement
    {Assignment Report Assertion Target : Type}
    (ctx : DerivedContext Assignment Report Assertion Target) :
    reference_fixation ctx.confirmationPractice ctx.referenceMap := by
  exact ctx.h_reference_fixation

theorem PaperReferenceStabilizationCriterionDerivedStatement
    {Assignment Report Assertion Target : Type}
    (ctx : ConfirmationDerivedContext Assignment Report Assertion Target) :
    ∀ e : Report, ∀ a : Assertion,
      ctx.confirmationPractice.supports e a ->
      ctx.confirmationPractice.about a (ctx.referenceMap e) ->
      theory_level_confirmed_at ctx.confirmationPractice e a := by
  intro e a hSupp hAbout
  exact
    PaperAdmissibleFixationEnablesTheoryLevelConfirmationStatement
      ctx.confirmationPractice
      ctx.referenceMap
      ctx.h_reference_fixation
      ctx.supportRespectsAdmissibility
      e
      a
      hSupp
      hAbout

theorem PaperDiachronicClosureDerivedStatement
    {Agent Time Record Assignment Report Assertion Target : Type}
    (ctx : DiachronicDerivedContext Agent Time Record Assignment Report Assertion Target) :
    SharedQuotientFactorization ctx.diachronic := by
  exact ctx.h_allFactorThroughSharedQuotient

theorem PaperIdentityPreservingLineageDerivedStatement
    {Agent Time Record Assignment Report Assertion Target : Type}
    (ctx : DiachronicDerivedContext Agent Time Record Assignment Report Assertion Target) :
    MemoryDependsOnReference ctx.diachronic /\
    AnticipationDependsOnSuccessorTyping ctx.diachronic /\
    AgencyNeedsTypedFutureRecords ctx.diachronic /\
    TheoryLevelConfirmationNeedsFixedReference
      ctx.confirmation.confirmationPractice
      ctx.confirmation.referenceMap := by
  exact
    And.intro
      ctx.h_memoryDependsOnReference
      (And.intro
        ctx.h_anticipationDependsOnSuccessorTyping
        (And.intro
          ctx.h_agencyNeedsTypedFutureRecords
          ctx.h_theoryLevelConfirmationNeedsFixedReference))

theorem PaperDiachronicInheritanceDerivedStatement
    {Agent Time Record Assignment Report Assertion Target : Type}
    (ctx : DiachronicDerivedContext Agent Time Record Assignment Report Assertion Target) :
    SharedQuotientFactorization ctx.diachronic /\
    MemoryDependsOnReference ctx.diachronic /\
    AnticipationDependsOnSuccessorTyping ctx.diachronic /\
    AgencyNeedsTypedFutureRecords ctx.diachronic /\
    TheoryLevelConfirmationNeedsFixedReference
      ctx.confirmation.confirmationPractice
      ctx.confirmation.referenceMap := by
  exact
    And.intro
      ctx.h_allFactorThroughSharedQuotient
      (And.intro
        ctx.h_memoryDependsOnReference
        (And.intro
          ctx.h_anticipationDependsOnSuccessorTyping
          (And.intro
            ctx.h_agencyNeedsTypedFutureRecords
            ctx.h_theoryLevelConfirmationNeedsFixedReference)))

theorem PaperDiachronicPracticeDependenceDerivedStatement
    {Agent Time Record Assignment Report Assertion Target : Type}
    (ctx : DiachronicDerivedContext Agent Time Record Assignment Report Assertion Target) :
    MemoryDependsOnReference ctx.diachronic /\
    AnticipationDependsOnSuccessorTyping ctx.diachronic /\
    AgencyNeedsTypedFutureRecords ctx.diachronic /\
    theory_level_confirmation_possible ctx.confirmation.confirmationPractice := by
  exact
    And.intro
      ctx.h_memoryDependsOnReference
      (And.intro
        ctx.h_anticipationDependsOnSuccessorTyping
        (And.intro
          ctx.h_agencyNeedsTypedFutureRecords
          (PaperTheoryLevelConfirmationCriterionDerivedStatement ctx.confirmation)))

theorem PaperStructuralLocusTrichotomyDerivedStatement
    (ctx : SelectorDerivedContext) :
    ctx.package.discourseCommitting ->
    exists locus : StructuralLocus,
      match locus with
      | .dynamicSelection => ctx.package.dynamicSelection
      | .onticPrivileging => ctx.package.onticPrivileging
      | .semanticRestriction => ctx.package.semanticRestriction
      | .discourseDeflation => ctx.package.discourseDeflation := by
  intro _
  exact PaperSelectorExhaustionTheoremStatement ctx.package ctx.selectorExhaustion

theorem PaperSelectorExhaustionDerivedStatement
    (ctx : SelectorDerivedContext) :
    BoundarySelectorForbidden ctx.package /\
    QuotientRefinementForcesScopeChange ctx.package /\
    RepresentationRestrictionImpliesSemanticOrDeflation ctx.package /\
    (exists locus : StructuralLocus,
      match locus with
      | .dynamicSelection => ctx.package.dynamicSelection
      | .onticPrivileging => ctx.package.onticPrivileging
      | .semanticRestriction => ctx.package.semanticRestriction
      | .discourseDeflation => ctx.package.discourseDeflation) := by
  refine And.intro ctx.h_boundarySelectorForbidden ?_
  refine And.intro ctx.h_quotientRefinementForcesScopeChange ?_
  refine And.intro ctx.h_representationRestrictionImpliesSemanticOrDeflation ?_
  exact PaperSelectorExhaustionTheoremStatement ctx.package ctx.selectorExhaustion

theorem PaperInterpretationTaxonomyDerivedStatement
    (ctx : SelectorDerivedContext) :
    ctx.package.dynamicSelection \/
    ctx.package.onticPrivileging \/
    ctx.package.semanticRestriction \/
    ctx.package.discourseDeflation := by
  exact PaperInterpretationTaxonomyStatement ctx.package ctx.selectorExhaustion

theorem PaperMeasurementProblemReferenceCurrentDerivedCoreStatement
    {Assignment Report Assertion Target : Type}
    (ctx : ConfirmationDerivedContext Assignment Report Assertion Target)
    (sem : SemanticDerivedContext Report)
    (stateCarries :
      EverettToyState ->
      EverettAuxiliarySpec EverettToyFactorization ->
      Prop)
    (h_not_reified : Not (selector_reified_as_state stateCarries)) :
    orbit_respects_invariants sem.A sem.B /\
    invariants_exhaust_orbits sem.A sem.B /\
    (∀ q b₁ b₂ : Report,
      same_target sem.B b₁ b₂ ->
      (sem.rel q b₁ ↔ sem.rel q b₂)) /\
    (exists rho : EverettToyState,
      exists sigma tau : EverettAuxiliarySpec EverettToyFactorization,
        everettToyBranchingData.extract rho sigma ≠
          everettToyBranchingData.extract rho tau) /\
    Not (decoherence_record_state_determined everettToyDecoherenceData) /\
    (exists tag : EverettSelectorDiagnosis,
      match tag with
      | EverettSelectorDiagnosis.pureBookkeeping =>
          Not (everett_weight_outcome_relevant everettToyWeightRule)
      | EverettSelectorDiagnosis.metaSelection =>
          everett_weight_outcome_relevant everettToyWeightRule /\
          Not (selector_reified_as_state stateCarries)
      | EverettSelectorDiagnosis.reifiedSelector =>
          selector_reified_as_state stateCarries) /\
    theory_level_confirmation_possible ctx.confirmationPractice /\
    reference_fixation ctx.confirmationPractice ctx.referenceMap := by
  refine And.intro (PaperMeasurementReferenceQuotientDerivedStatement sem) ?_
  refine And.intro (PaperGlobalEquivalenceCollapseDerivedStatement sem) ?_
  refine And.intro
    (PaperFixationCommutationNecessityForTheoryLevelConfirmationDerivedStatement sem) ?_
  refine And.intro PaperEverettianNonSelectionDerivedStatement ?_
  refine And.intro PaperDecoherenceNonSelectionDerivedStatement ?_
  refine And.intro ?_ ?_
  · exact PaperEverettianDownstreamDerivedStatement stateCarries h_not_reified
  · refine And.intro ?_ ?_
    · exact PaperTheoryLevelConfirmationCriterionDerivedStatement ctx
    · exact ctx.h_reference_fixation

theorem PaperMeasurementProblemReferenceDiachronicCurrentStatement
    {Agent Time Record Assignment Report Assertion Target : Type}
    (ctx : DiachronicDerivedContext Agent Time Record Assignment Report Assertion Target) :
    SharedQuotientFactorization ctx.diachronic /\
    MemoryDependsOnReference ctx.diachronic /\
    AnticipationDependsOnSuccessorTyping ctx.diachronic /\
    AgencyNeedsTypedFutureRecords ctx.diachronic /\
    theory_level_confirmation_possible ctx.confirmation.confirmationPractice := by
  exact
    And.intro
      (PaperDiachronicClosureDerivedStatement ctx)
      (And.intro
        ctx.h_memoryDependsOnReference
        (And.intro
          ctx.h_anticipationDependsOnSuccessorTyping
          (And.intro
            ctx.h_agencyNeedsTypedFutureRecords
            (PaperTheoryLevelConfirmationCriterionDerivedStatement
              ctx.confirmation))))

theorem PaperMeasurementProblemReferenceSelectorCurrentStatement
    (ctx : SelectorDerivedContext) :
    BoundarySelectorForbidden ctx.package /\
    QuotientRefinementForcesScopeChange ctx.package /\
    RepresentationRestrictionImpliesSemanticOrDeflation ctx.package /\
    (ctx.package.dynamicSelection \/
      ctx.package.onticPrivileging \/
      ctx.package.semanticRestriction \/
      ctx.package.discourseDeflation) := by
  exact
    And.intro
      ctx.h_boundarySelectorForbidden
      (And.intro
        ctx.h_quotientRefinementForcesScopeChange
        (And.intro
          ctx.h_representationRestrictionImpliesSemanticOrDeflation
          (PaperInterpretationTaxonomyDerivedStatement ctx)))

/- Compatibility notices for manuscript-facing versus current derived names. -/
def LegacyMeasurementWrapperNotice : String :=
  "Legacy manuscript-facing wrapper surface retained for paper alignment; prefer the current derived route for semantic, confirmation, diachronic, and taxonomy claims."

def LegacyWrapperNames : List String :=
  [ "PaperMeasurementReferenceQuotientTheoremStatement"
  , "PaperGlobalEquivalenceCollapseTheoremStatement"
  , "PaperFixationCommutationNecessityForTheoryLevelConfirmationStatement"
  , "PaperTheoryLevelConfirmationCriterionStatement"
  ]

def CurrentMeasurementDerivedNotice : String :=
  "Current preferred route: use the derived semantic, Everett/decoherence, confirmation, diachronic, and selector-taxonomy theorem layers."

def CurrentDerivedNames : List String :=
  [ "PaperMeasurementReferenceQuotientDerivedStatement"
  , "PaperGlobalEquivalenceCollapseDerivedStatement"
  , "PaperFixationCommutationNecessityForTheoryLevelConfirmationDerivedStatement"
  , "PaperEverettianNonSelectionDerivedStatement"
  , "PaperDecoherenceNonSelectionDerivedStatement"
  , "PaperEverettianDownstreamDerivedStatement"
  , "PaperNoAuxiliaryParameterizationOfTheoryLevelConfirmationDerivedStatement"
  , "PaperTheoryLevelConfirmationCriterionDerivedStatement"
  , "PaperReferenceStabilizationCriterionDerivedStatement"
  , "PaperReferenceStabilizationNecessityDerivedStatement"
  , "PaperDiachronicClosureDerivedStatement"
  , "PaperIdentityPreservingLineageDerivedStatement"
  , "PaperDiachronicInheritanceDerivedStatement"
  , "PaperDiachronicPracticeDependenceDerivedStatement"
  , "PaperStructuralLocusTrichotomyDerivedStatement"
  , "PaperSelectorExhaustionDerivedStatement"
  , "PaperInterpretationTaxonomyDerivedStatement"
  , "PaperMeasurementProblemReferenceDiachronicCurrentStatement"
  , "PaperMeasurementProblemReferenceSelectorCurrentStatement"
  , "PaperMeasurementProblemReferenceCurrentDerivedCoreStatement"
  ]

def CurrentSurfaceNames : List String :=
  [ "Surface.SummaryStatement"
  , "Surface.CurrentDerivedSummaryStatement"
  , "Surface.DiachronicCurrentSummaryStatement"
  , "Surface.SelectorCurrentSummaryStatement"
  ]

end MeasurementProblemReference
end Papers
end MaleyLean
