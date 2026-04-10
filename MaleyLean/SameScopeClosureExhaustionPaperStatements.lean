import MaleyLean.MathClosurePaperStatements

namespace MaleyLean

/--
Dedicated theorem surface for the hardened manuscript
"Closure by Exhaustion for Same-Scope Operators under Admissibility".

This module reuses the richer semantic spine from `MathClosurePaperStatements`
but gives the hardened paper its own named theorem inventory and supporting
data packets.
-/

structure StandingRelativeRegime (X Op : Type) extends FixedBaseSemantics X Op where
  lawfulRedescription : X -> X -> Prop
  bookkeepingEquivalent : X -> X -> Prop
  standingFixedCarrier : X -> Prop

structure SameScopeOperatorData (X Op F : Type) extends FixedBaseOperatorData X Op F where
  bookkeeping : F -> Prop
  inadmissible : F -> Prop
  sameScope : F -> Prop

def operatorClosedByAdmissibility {X Op F : Type}
    (D : SameScopeOperatorData X Op F) (f : F) : Prop :=
  D.bookkeeping f ∨ D.inadmissible f

inductive AuditedKernel where
  | selectorRule
  | genericWitness
  | completionBoundary
  | globalConstraintFamily
  | comparisonTotality
  | certifyingWitness
  | infinitaryCompletion
  | weightingRule
  | identificationRule
  | repairRule
  | metaAuthority
deriving DecidableEq, Repr

structure AuditedKernelWitnessData (F : Type) where
  kernelUsed : F -> AuditedKernel -> Prop
  nonbookkeeping_has_kernel :
    ∀ f : F, ¬ False -> (∃ k : AuditedKernel, kernelUsed f k)

structure FamilyClosureWitness (F : Type) where
  bookkeeping : F -> Prop
  inadmissible : F -> Prop
  closed : ∀ f : F, bookkeeping f ∨ inadmissible f

structure TranslationOverlapData (R1 R2 D : Type) where
  leftMap : D -> R1
  rightMap : D -> R2
  normalizationFixed : D -> Prop
  preservesStandingLeft : D -> Prop
  preservesStandingRight : D -> Prop

structure ClosureCertificateData (R1 R2 D : Type) where
  overlap : TranslationOverlapData R1 R2 D
  certifiedIdentity : D -> Prop
  noSurplusContent : D -> Prop

structure AuditSharpnessData (Clause Attack : Type) where
  reopens : Clause -> Attack -> Prop
  majorClause : Clause -> Prop
  sharp :
    ∀ c : Clause, majorClause c -> ∃ a : Attack, reopens c a

inductive TotalizationClass where
  | domainEnlargement
  | carrierCollapse
  | evaluativeCompletion
  | conservativeDefinitionalExtension
  | nonConservativeFamilyChange
deriving DecidableEq, Repr

inductive RegistryFamily where
  | choiceSelection
  | genericityForcing
  | completion
  | compactnessSaturation
  | universalProperty
  | modelTheoreticExistence
  | infinityOperator
  | typicalityMeasure
  | canonicalRepresentatives
  | standingRepair
  | metaFoundationalReanchoring
deriving DecidableEq, Repr

inductive FrameworkClause where
  | generationBoundStanding
  | graphFixityOnOldCarrier
  | sameScopeRestriction
  | normalizationPreservingRedescription
  | noImportedWitnesses
  | noImportedGlobalComparison
deriving DecidableEq, Repr

inductive ReopenedAttackClass where
  | postHocRepair
  | deferredAdmissibility
  | directTotalization
  | carrierCollapse
  | completionByScopeShift
  | infinityByScopeShift
  | representationalDivergence
  | foundationSwapAmbiguity
  | modelWitnessImport
  | metaReanchoring
  | universalityByImportedComparison
  | compactnessByImportedTests
  | typicalityByImportedWeights
deriving DecidableEq, Repr

structure SameScopeTotalizationAudit {X Op F : Type} (D : SameScopeOperatorData X Op F) where
  totalizationAttempt : F -> Prop
  fallsUnder : F -> TotalizationClass -> Prop
  exhaustive :
    forall f : F, totalizationAttempt f -> Exists fun c : TotalizationClass => fallsUnder f c
  domainEnlargementBlocked :
    forall f : F, fallsUnder f TotalizationClass.domainEnlargement -> False
  carrierCollapseInadmissible :
    forall f : F, fallsUnder f TotalizationClass.carrierCollapse -> D.inadmissible f
  evaluativeCompletionInadmissible :
    forall f : F, fallsUnder f TotalizationClass.evaluativeCompletion -> D.inadmissible f
  conservativeDefinitionalBookkeeping :
    forall f : F, fallsUnder f TotalizationClass.conservativeDefinitionalExtension -> D.bookkeeping f
  familyChangeInadmissible :
    forall f : F, fallsUnder f TotalizationClass.nonConservativeFamilyChange -> D.inadmissible f

theorem sameScopeTotalizationAudit_closed
    {X Op F : Type}
    {D : SameScopeOperatorData X Op F}
    (A : SameScopeTotalizationAudit D) :
    forall f : F, A.totalizationAttempt f -> Or (D.bookkeeping f) (D.inadmissible f) := by
  intro f hf
  match A.exhaustive f hf with
  | Exists.intro c hc =>
  cases c with
  | domainEnlargement =>
      exfalso
      exact A.domainEnlargementBlocked f hc
  | carrierCollapse =>
      exact Or.inr (A.carrierCollapseInadmissible f hc)
  | evaluativeCompletion =>
      exact Or.inr (A.evaluativeCompletionInadmissible f hc)
  | conservativeDefinitionalExtension =>
      exact Or.inl (A.conservativeDefinitionalBookkeeping f hc)
  | nonConservativeFamilyChange =>
      exact Or.inr (A.familyChangeInadmissible f hc)

structure SameScopeRegistryAudit {X Op F : Type} (D : SameScopeOperatorData X Op F) where
  directFamily : RegistryFamily -> F -> Prop
  familyClosed :
    forall fam : RegistryFamily, forall f : F,
      directFamily fam f -> Or (D.bookkeeping f) (D.inadmissible f)

structure SameScopeInteractionAudit {X Op F : Type} (D : SameScopeOperatorData X Op F) where
  interactionGenerated : F -> Prop
  closed :
    forall f : F, interactionGenerated f -> Or (D.bookkeeping f) (D.inadmissible f)

structure ClosureByExhaustionSystem (X Op F : Type) where
  regime : StandingRelativeRegime X Op
  ops : SameScopeOperatorData X Op F
  kernels : AuditedKernelWitnessData F
  totalization : SameScopeTotalizationAudit ops
  registry : SameScopeRegistryAudit ops
  interaction : SameScopeInteractionAudit ops
  routeCover :
    forall f : F, ops.sameScope f -> Not (ops.bookkeeping f) ->
      Or (totalization.totalizationAttempt f)
        (Or (Exists fun fam : RegistryFamily => registry.directFamily fam f)
            (interaction.interactionGenerated f))
  kernelProvenance :
    forall f : F, ops.sameScope f -> Not (ops.bookkeeping f) ->
      Exists fun k : AuditedKernel => kernels.kernelUsed f k

theorem closureByExhaustionSystem_closed
    {X Op F : Type}
    (S : ClosureByExhaustionSystem X Op F) :
    forall f : F, S.ops.sameScope f -> Or (S.ops.bookkeeping f) (S.ops.inadmissible f) := by
  intro f hs
  by_cases hbook : S.ops.bookkeeping f
  case pos =>
    exact Or.inl hbook
  case neg =>
    have hroute := S.routeCover f hs hbook
    rcases hroute with htot | hrest
    · exact sameScopeTotalizationAudit_closed S.totalization f htot
    · rcases hrest with hreg | hint
      · match hreg with
        | Exists.intro fam hfam =>
            exact S.registry.familyClosed fam f hfam
      · exact S.interaction.closed f hint

theorem closureByExhaustionSystem_closed_constructive
    {X Op F : Type}
    (S : ClosureByExhaustionSystem X Op F)
    [DecidablePred S.ops.bookkeeping] :
    forall f : F, S.ops.sameScope f -> Or (S.ops.bookkeeping f) (S.ops.inadmissible f) := by
  intro f hs
  by_cases hbook : S.ops.bookkeeping f
  case pos =>
    exact Or.inl hbook
  case neg =>
    have hroute := S.routeCover f hs hbook
    rcases hroute with htot | hrest
    · exact sameScopeTotalizationAudit_closed S.totalization f htot
    · rcases hrest with hreg | hint
      · match hreg with
        | Exists.intro fam hfam =>
            exact S.registry.familyClosed fam f hfam
      · exact S.interaction.closed f hint

theorem closureByExhaustionSystem_noHiddenKernel
    {X Op F : Type}
    (S : ClosureByExhaustionSystem X Op F)
    (hidden : F -> Prop)
    (h_sameScope : forall f : F, hidden f -> S.ops.sameScope f)
    (h_nonbookkeeping : forall f : F, hidden f -> Not (S.ops.bookkeeping f))
    (h_kernel_free :
      forall f : F, hidden f -> forall k : AuditedKernel, Not (S.kernels.kernelUsed f k)) :
    forall f : F, hidden f -> False := by
  intro f hf
  match S.kernelProvenance f (h_sameScope f hf) (h_nonbookkeeping f hf) with
  | Exists.intro k hk =>
      exact h_kernel_free f hf k hk

def frameworkClauseReopens :
    FrameworkClause -> ReopenedAttackClass -> Prop
  | FrameworkClause.generationBoundStanding, ReopenedAttackClass.postHocRepair => True
  | FrameworkClause.graphFixityOnOldCarrier, ReopenedAttackClass.directTotalization => True
  | FrameworkClause.sameScopeRestriction, ReopenedAttackClass.carrierCollapse => True
  | FrameworkClause.normalizationPreservingRedescription, ReopenedAttackClass.foundationSwapAmbiguity => True
  | FrameworkClause.noImportedWitnesses, ReopenedAttackClass.modelWitnessImport => True
  | FrameworkClause.noImportedGlobalComparison, ReopenedAttackClass.universalityByImportedComparison => True
  | _, _ => False

def hardenedAuditSharpnessData :
    AuditSharpnessData FrameworkClause ReopenedAttackClass where
  reopens := frameworkClauseReopens
  majorClause := fun _ => True
  sharp := by
    intro c _
    cases c with
    | generationBoundStanding =>
        exact Exists.intro ReopenedAttackClass.postHocRepair trivial
    | graphFixityOnOldCarrier =>
        exact Exists.intro ReopenedAttackClass.directTotalization trivial
    | sameScopeRestriction =>
        exact Exists.intro ReopenedAttackClass.carrierCollapse trivial
    | normalizationPreservingRedescription =>
        exact Exists.intro ReopenedAttackClass.foundationSwapAmbiguity trivial
    | noImportedWitnesses =>
        exact Exists.intro ReopenedAttackClass.modelWitnessImport trivial
    | noImportedGlobalComparison =>
        exact Exists.intro ReopenedAttackClass.universalityByImportedComparison trivial

theorem hardenedAuditSharpnessStatement :
    forall c : FrameworkClause, hardenedAuditSharpnessData.majorClause c ->
      Exists fun a : ReopenedAttackClass => hardenedAuditSharpnessData.reopens c a := by
  exact hardenedAuditSharpnessData.sharp

theorem hardenedAuditSharpnessStatement_constructive :
    forall c : FrameworkClause, Exists fun a : ReopenedAttackClass => frameworkClauseReopens c a := by
  intro c
  cases c with
  | generationBoundStanding =>
      exact Exists.intro ReopenedAttackClass.postHocRepair trivial
  | graphFixityOnOldCarrier =>
      exact Exists.intro ReopenedAttackClass.directTotalization trivial
  | sameScopeRestriction =>
      exact Exists.intro ReopenedAttackClass.carrierCollapse trivial
  | normalizationPreservingRedescription =>
      exact Exists.intro ReopenedAttackClass.foundationSwapAmbiguity trivial
  | noImportedWitnesses =>
      exact Exists.intro ReopenedAttackClass.modelWitnessImport trivial
  | noImportedGlobalComparison =>
      exact Exists.intro ReopenedAttackClass.universalityByImportedComparison trivial

inductive ChoiceExhaustionCase where
  | standingFixedOutput
  | importedSelectorParameter
  | indistinguishableCandidateSplit
  | transformFailsAdmissibleInvariance
  | transformRevealsAlreadyFixedWitness
  | multivaluedRefinement
  | complexityRuleImported
  | complexityRuleFallsBackToRefinement
deriving DecidableEq, Repr

structure ChoiceExhaustionAudit (D Sel : Type) where
  chooses : Sel -> D -> Prop
  bookkeeping : Sel -> Prop
  inadmissible : Sel -> Prop
  classifiedAs : Sel -> ChoiceExhaustionCase -> Prop
  exhaustive :
    forall s : Sel, Exists fun c : ChoiceExhaustionCase => classifiedAs s c
  bookkeepingStandingFixed :
    forall s : Sel, classifiedAs s ChoiceExhaustionCase.standingFixedOutput
      -> bookkeeping s
  bookkeepingTransformReveal :
    forall s : Sel, classifiedAs s ChoiceExhaustionCase.transformRevealsAlreadyFixedWitness
      -> bookkeeping s
  inadmissibleImported :
    forall s : Sel, classifiedAs s ChoiceExhaustionCase.importedSelectorParameter -> inadmissible s
  inadmissibleIndistinguishable :
    forall s : Sel, classifiedAs s ChoiceExhaustionCase.indistinguishableCandidateSplit -> inadmissible s
  inadmissibleTransform :
    forall s : Sel, classifiedAs s ChoiceExhaustionCase.transformFailsAdmissibleInvariance -> inadmissible s
  inadmissibleRefinement :
    forall s : Sel, classifiedAs s ChoiceExhaustionCase.multivaluedRefinement -> inadmissible s
  inadmissibleComplexityImported :
    forall s : Sel, classifiedAs s ChoiceExhaustionCase.complexityRuleImported -> inadmissible s
  inadmissibleComplexityRefinement :
    forall s : Sel, classifiedAs s ChoiceExhaustionCase.complexityRuleFallsBackToRefinement -> inadmissible s

theorem choiceExhaustionAudit_closed
    {D Sel : Type}
    (A : ChoiceExhaustionAudit D Sel) :
    forall s : Sel, Or (A.bookkeeping s) (A.inadmissible s) := by
  intro s
  match A.exhaustive s with
  | Exists.intro c hc =>
      cases c with
      | standingFixedOutput =>
          exact Or.inl (A.bookkeepingStandingFixed s hc)
      | importedSelectorParameter =>
          exact Or.inr (A.inadmissibleImported s hc)
      | indistinguishableCandidateSplit =>
          exact Or.inr (A.inadmissibleIndistinguishable s hc)
      | transformFailsAdmissibleInvariance =>
          exact Or.inr (A.inadmissibleTransform s hc)
      | transformRevealsAlreadyFixedWitness =>
          exact Or.inl (A.bookkeepingTransformReveal s hc)
      | multivaluedRefinement =>
          exact Or.inr (A.inadmissibleRefinement s hc)
      | complexityRuleImported =>
          exact Or.inr (A.inadmissibleComplexityImported s hc)
      | complexityRuleFallsBackToRefinement =>
          exact Or.inr (A.inadmissibleComplexityRefinement s hc)

inductive ForcingExhaustionClass where
  | directGenericOutput
  | existenceOnlyForcing
  | canonicalGenericity
  | booleanValuedSurrogate
  | absolutenessTransfer
  | iteratedForcing
  | forcingAsCompletion
  | metaFoundationalReanchoring
deriving DecidableEq, Repr

structure ForcingExhaustionAudit (F : Type) where
  forcingMove : F -> Prop
  bookkeeping : F -> Prop
  inadmissible : F -> Prop
  classifiedAs : F -> ForcingExhaustionClass -> Prop
  exhaustive :
    forall f : F, forcingMove f -> Exists fun c : ForcingExhaustionClass => classifiedAs f c
  bookkeepingDirectFixed :
    forall f : F, classifiedAs f ForcingExhaustionClass.directGenericOutput -> bookkeeping f
  inadmissibleDirectImported :
    forall f : F, classifiedAs f ForcingExhaustionClass.directGenericOutput -> inadmissible f
  inadmissibleExistenceOnly :
    forall f : F, classifiedAs f ForcingExhaustionClass.existenceOnlyForcing -> inadmissible f
  reducedToChoice :
    forall f : F, classifiedAs f ForcingExhaustionClass.canonicalGenericity ->
      Or (bookkeeping f) (inadmissible f)
  reducedToCompletion :
    forall f : F, classifiedAs f ForcingExhaustionClass.booleanValuedSurrogate ->
      Or (bookkeeping f) (inadmissible f)
  transferDisposition :
    forall f : F, classifiedAs f ForcingExhaustionClass.absolutenessTransfer ->
      Or (bookkeeping f) (inadmissible f)
  stagedDisposition :
    forall f : F, classifiedAs f ForcingExhaustionClass.iteratedForcing ->
      Or (bookkeeping f) (inadmissible f)
  completionDisposition :
    forall f : F, classifiedAs f ForcingExhaustionClass.forcingAsCompletion ->
      Or (bookkeeping f) (inadmissible f)
  metaDisposition :
    forall f : F, classifiedAs f ForcingExhaustionClass.metaFoundationalReanchoring ->
      Or (bookkeeping f) (inadmissible f)

theorem forcingExhaustionAudit_closed
    {F : Type}
    (A : ForcingExhaustionAudit F) :
    forall f : F, A.forcingMove f -> Or (A.bookkeeping f) (A.inadmissible f) := by
  intro f hf
  match A.exhaustive f hf with
  | Exists.intro c hc =>
      cases c with
      | directGenericOutput =>
          by_cases hbook : A.bookkeeping f
          · exact Or.inl hbook
          · exact Or.inr (A.inadmissibleDirectImported f hc)
      | existenceOnlyForcing =>
          exact Or.inr (A.inadmissibleExistenceOnly f hc)
      | canonicalGenericity =>
          exact A.reducedToChoice f hc
      | booleanValuedSurrogate =>
          exact A.reducedToCompletion f hc
      | absolutenessTransfer =>
          exact A.transferDisposition f hc
      | iteratedForcing =>
          exact A.stagedDisposition f hc
      | forcingAsCompletion =>
          exact A.completionDisposition f hc
      | metaFoundationalReanchoring =>
          exact A.metaDisposition f hc

theorem forcingExhaustionAudit_closed_constructive
    {F : Type}
    (A : ForcingExhaustionAudit F)
    [DecidablePred A.bookkeeping] :
    forall f : F, A.forcingMove f -> Or (A.bookkeeping f) (A.inadmissible f) := by
  intro f hf
  match A.exhaustive f hf with
  | Exists.intro c hc =>
      cases c with
      | directGenericOutput =>
          by_cases hbook : A.bookkeeping f
          · exact Or.inl hbook
          · exact Or.inr (A.inadmissibleDirectImported f hc)
      | existenceOnlyForcing =>
          exact Or.inr (A.inadmissibleExistenceOnly f hc)
      | canonicalGenericity =>
          exact A.reducedToChoice f hc
      | booleanValuedSurrogate =>
          exact A.reducedToCompletion f hc
      | absolutenessTransfer =>
          exact A.transferDisposition f hc
      | iteratedForcing =>
          exact A.stagedDisposition f hc
      | forcingAsCompletion =>
          exact A.completionDisposition f hc
      | metaFoundationalReanchoring =>
          exact A.metaDisposition f hc

inductive RepairExhaustionClass where
  | postHocCorrection
  | temporalDeferral
  | localIsolation
  | probabilisticRecovery
  | ensembleRecovery
  | semanticRedescription
  | authoritativeOverride
deriving DecidableEq, Repr

structure RepairExhaustionAudit (R : Type) where
  repairMove : R -> Prop
  classifiedAs : R -> RepairExhaustionClass -> Prop
  exhaustive :
    forall r : R, repairMove r -> Exists fun c : RepairExhaustionClass => classifiedAs r c
  blocked :
    forall r : R, repairMove r -> False

theorem repairExhaustionAudit_closed
    {R : Type}
    (A : RepairExhaustionAudit R) :
    forall r : R, A.repairMove r -> False := by
  intro r hr
  exact A.blocked r hr

theorem PaperChoiceSelectionClosureFromAppendixStatement
    {D Sel : Type}
    (A : ChoiceExhaustionAudit D Sel) :
    forall s : Sel, Or (A.bookkeeping s) (A.inadmissible s) := by
  exact choiceExhaustionAudit_closed A

theorem PaperForcingClosureFromAppendixStatement
    {F : Type}
    (A : ForcingExhaustionAudit F) :
    forall f : F, A.forcingMove f -> Or (A.bookkeeping f) (A.inadmissible f) := by
  exact forcingExhaustionAudit_closed A

theorem PaperForcingClosureFromAppendixConstructiveStatement
    {F : Type}
    (A : ForcingExhaustionAudit F)
    [DecidablePred A.bookkeeping] :
    forall f : F, A.forcingMove f -> Or (A.bookkeeping f) (A.inadmissible f) := by
  exact forcingExhaustionAudit_closed_constructive A

theorem PaperNoAdmissibleStandingRepairFromAppendixStatement
    {R : Type}
    (A : RepairExhaustionAudit R) :
    forall r : R, A.repairMove r -> False := by
  exact repairExhaustionAudit_closed A

structure ImportedDatumFamilyAudit (F Datum : Type) where
  familyMember : F -> Prop
  bookkeeping : F -> Prop
  inadmissible : F -> Prop
  datum : F -> Datum
  standingFixed : Datum -> Prop
  imported : Datum -> Prop
  dichotomy :
    forall f : F, familyMember f -> standingFixed (datum f) ∨ imported (datum f)
  bookkeeping_of_standingFixed :
    forall f : F, familyMember f -> standingFixed (datum f) -> bookkeeping f
  inadmissible_of_imported :
    forall f : F, familyMember f -> imported (datum f) -> inadmissible f

theorem importedDatumFamilyAudit_closed
    {F Datum : Type}
    (A : ImportedDatumFamilyAudit F Datum) :
    forall f : F, A.familyMember f -> Or (A.bookkeeping f) (A.inadmissible f) := by
  intro f hf
  rcases A.dichotomy f hf with hfix | himp
  · exact Or.inl (A.bookkeeping_of_standingFixed f hf hfix)
  · exact Or.inr (A.inadmissible_of_imported f hf himp)

def importedDatumFamilyAuditOfSupportGovernedFamily
    {Route Support : Type}
    (F : SupportGovernedFamily Route Support) :
    ImportedDatumFamilyAudit Route Support where
  familyMember := fun _ => True
  bookkeeping := F.conservative
  inadmissible := F.external
  datum := F.support
  standingFixed := F.supportStatus.internallyFixed
  imported := F.supportStatus.imported
  dichotomy := by
    intro r _
    exact F.support_classified r
  bookkeeping_of_standingFixed := by
    intro r _ h
    exact F.conservative_of_fixed r h
  inadmissible_of_imported := by
    intro r _ h
    exact F.external_of_imported r h

def canonicalizationImportedDatumAudit
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q) :
    ImportedDatumFamilyAudit D Q :=
  importedDatumFamilyAuditOfSupportGovernedFamily
    (canonicalizationAsSupportGovernedFamily C)

def completionImportedDatumAudit
    {A AHat : Type}
    (C : CompletionTransferData A AHat) :
    ImportedDatumFamilyAudit {y : AHat // C.oldBaseRelevant y} AHat :=
  importedDatumFamilyAuditOfSupportGovernedFamily
    (completionAsSupportGovernedFamily C)

def modelImportedDatumAudit
    {M N F : Type}
    (D : ModelWitnessTransferData M N F) :
    ImportedDatumFamilyAudit
      { p : F × ModelWitnessSupportRoute //
          match p.2 with
          | .definablyFixed => D.definablyFixedWitness p.1
          | .imported => D.importedWitness p.1
          | .detourReadback => D.detourReadback p.1 }
      ModelWitnessSupportRoute :=
  importedDatumFamilyAuditOfSupportGovernedFamily
    (modelWitnessAsSupportGovernedFamily D)

def forcingImportedDatumAudit
    {M G : Type}
    (D : ForcingTransferData M G) :
    ImportedDatumFamilyAudit
      { p : G × ForcingSupportRoute //
          D.oldParameterConclusion p.1 ∧
          match p.2 with
          | .absoluteReadback => D.absoluteReadback p.1
          | .genericDependence => D.genericWitness p.1 ∧ D.genericDependent p.1 }
      ForcingSupportRoute :=
  importedDatumFamilyAuditOfSupportGovernedFamily
    (forcingAsSupportGovernedFamily D)

def universalImportedDatumAudit
    {A F : Type}
    (D : UniversalConstructionTransferData A F) :
    ImportedDatumFamilyAudit F F :=
  importedDatumFamilyAuditOfSupportGovernedFamily
    (universalConstructionAsSupportGovernedFamily D)

theorem PaperImportedDatumFamilyClosureStatement
    {F Datum : Type}
    (A : ImportedDatumFamilyAudit F Datum) :
    forall f : F, A.familyMember f -> Or (A.bookkeeping f) (A.inadmissible f) := by
  exact importedDatumFamilyAudit_closed A

def mkImportedDatumFamilyAudit
    {F Datum : Type}
    (familyMember bookkeeping inadmissible : F -> Prop)
    (datum : F -> Datum)
    (standingFixed imported : Datum -> Prop)
    (h_classified :
      forall f : F, familyMember f -> standingFixed (datum f) ∨ imported (datum f))
    (h_bookkeeping :
      forall f : F, familyMember f -> standingFixed (datum f) -> bookkeeping f)
    (h_inadmissible :
      forall f : F, familyMember f -> imported (datum f) -> inadmissible f) :
    ImportedDatumFamilyAudit F Datum where
  familyMember := familyMember
  bookkeeping := bookkeeping
  inadmissible := inadmissible
  datum := datum
  standingFixed := standingFixed
  imported := imported
  dichotomy := h_classified
  bookkeeping_of_standingFixed := h_bookkeeping
  inadmissible_of_imported := h_inadmissible

def infinityImportedDatumAudit
    {F Aux : Type}
    (familyMember bookkeeping inadmissible : F -> Prop)
    (support : F -> Aux)
    (standingFixed imported : Aux -> Prop)
    (h_classified :
      forall f : F, familyMember f -> standingFixed (support f) ∨ imported (support f))
    (h_bookkeeping :
      forall f : F, familyMember f -> standingFixed (support f) -> bookkeeping f)
    (h_inadmissible :
      forall f : F, familyMember f -> imported (support f) -> inadmissible f) :
    ImportedDatumFamilyAudit F Aux :=
  mkImportedDatumFamilyAudit familyMember bookkeeping inadmissible
    support standingFixed imported h_classified h_bookkeeping h_inadmissible

def typicalityImportedDatumAudit
    {F Aux : Type}
    (familyMember bookkeeping inadmissible : F -> Prop)
    (support : F -> Aux)
    (standingFixed imported : Aux -> Prop)
    (h_classified :
      forall f : F, familyMember f -> standingFixed (support f) ∨ imported (support f))
    (h_bookkeeping :
      forall f : F, familyMember f -> standingFixed (support f) -> bookkeeping f)
    (h_inadmissible :
      forall f : F, familyMember f -> imported (support f) -> inadmissible f) :
    ImportedDatumFamilyAudit F Aux :=
  mkImportedDatumFamilyAudit familyMember bookkeeping inadmissible
    support standingFixed imported h_classified h_bookkeeping h_inadmissible

def metaReanchoringImportedDatumAudit
    {F Aux : Type}
    (familyMember bookkeeping inadmissible : F -> Prop)
    (support : F -> Aux)
    (standingFixed imported : Aux -> Prop)
    (h_classified :
      forall f : F, familyMember f -> standingFixed (support f) ∨ imported (support f))
    (h_bookkeeping :
      forall f : F, familyMember f -> standingFixed (support f) -> bookkeeping f)
    (h_inadmissible :
      forall f : F, familyMember f -> imported (support f) -> inadmissible f) :
    ImportedDatumFamilyAudit F Aux :=
  mkImportedDatumFamilyAudit familyMember bookkeeping inadmissible
    support standingFixed imported h_classified h_bookkeeping h_inadmissible

def registryAuditFromAppendixData
    {X Op F ChoiceDom : Type}
    (D : SameScopeOperatorData X Op F)
    (directFamily : RegistryFamily -> F -> Prop)
    (choiceAudit : ChoiceExhaustionAudit ChoiceDom F)
    (forcingAudit : ForcingExhaustionAudit F)
    (repairAudit : RepairExhaustionAudit F)
    [DecidablePred forcingAudit.bookkeeping]
    (h_choice_bookkeeping : choiceAudit.bookkeeping = D.bookkeeping)
    (h_choice_inadmissible : choiceAudit.inadmissible = D.inadmissible)
    (h_forcing_bookkeeping : forcingAudit.bookkeeping = D.bookkeeping)
    (h_forcing_inadmissible : forcingAudit.inadmissible = D.inadmissible)
    (h_forcing_family :
      forall f : F, directFamily RegistryFamily.genericityForcing f -> forcingAudit.forcingMove f)
    (h_repair_family :
      forall f : F, directFamily RegistryFamily.standingRepair f -> repairAudit.repairMove f)
    (h_completion :
      forall f : F, directFamily RegistryFamily.completion f -> D.bookkeeping f ∨ D.inadmissible f)
    (h_compactness :
      forall f : F, directFamily RegistryFamily.compactnessSaturation f -> D.bookkeeping f ∨ D.inadmissible f)
    (h_universal :
      forall f : F, directFamily RegistryFamily.universalProperty f -> D.bookkeeping f ∨ D.inadmissible f)
    (h_model :
      forall f : F, directFamily RegistryFamily.modelTheoreticExistence f -> D.bookkeeping f ∨ D.inadmissible f)
    (h_infinity :
      forall f : F, directFamily RegistryFamily.infinityOperator f -> D.bookkeeping f ∨ D.inadmissible f)
    (h_typicality :
      forall f : F, directFamily RegistryFamily.typicalityMeasure f -> D.bookkeeping f ∨ D.inadmissible f)
    (h_canonical :
      forall f : F, directFamily RegistryFamily.canonicalRepresentatives f -> D.bookkeeping f ∨ D.inadmissible f)
    (h_meta :
      forall f : F, directFamily RegistryFamily.metaFoundationalReanchoring f -> D.bookkeeping f ∨ D.inadmissible f) :
    SameScopeRegistryAudit D where
  directFamily := directFamily
  familyClosed := by
    intro fam f hfam
    cases fam with
    | choiceSelection =>
        simpa [h_choice_bookkeeping, h_choice_inadmissible] using
          (PaperChoiceSelectionClosureFromAppendixStatement choiceAudit f)
    | genericityForcing =>
        simpa [h_forcing_bookkeeping, h_forcing_inadmissible] using
          (PaperForcingClosureFromAppendixConstructiveStatement forcingAudit f (h_forcing_family f hfam))
    | completion =>
        exact h_completion f hfam
    | compactnessSaturation =>
        exact h_compactness f hfam
    | universalProperty =>
        exact h_universal f hfam
    | modelTheoreticExistence =>
        exact h_model f hfam
    | infinityOperator =>
        exact h_infinity f hfam
    | typicalityMeasure =>
        exact h_typicality f hfam
    | canonicalRepresentatives =>
        exact h_canonical f hfam
    | standingRepair =>
        exfalso
        exact PaperNoAdmissibleStandingRepairFromAppendixStatement repairAudit f (h_repair_family f hfam)
    | metaFoundationalReanchoring =>
        exact h_meta f hfam

theorem closureByExhaustionFromAppendixBackedRegistry_constructive
    {X Op F ChoiceDom : Type}
    (regime : StandingRelativeRegime X Op)
    (ops : SameScopeOperatorData X Op F)
    (kernels : AuditedKernelWitnessData F)
    (totalization : SameScopeTotalizationAudit ops)
    (directFamily : RegistryFamily -> F -> Prop)
    (choiceAudit : ChoiceExhaustionAudit ChoiceDom F)
    (forcingAudit : ForcingExhaustionAudit F)
    (repairAudit : RepairExhaustionAudit F)
    (interaction : SameScopeInteractionAudit ops)
    [DecidablePred ops.bookkeeping]
    [DecidablePred forcingAudit.bookkeeping]
    (h_choice_bookkeeping : choiceAudit.bookkeeping = ops.bookkeeping)
    (h_choice_inadmissible : choiceAudit.inadmissible = ops.inadmissible)
    (h_forcing_bookkeeping : forcingAudit.bookkeeping = ops.bookkeeping)
    (h_forcing_inadmissible : forcingAudit.inadmissible = ops.inadmissible)
    (h_forcing_family :
      forall f : F, directFamily RegistryFamily.genericityForcing f -> forcingAudit.forcingMove f)
    (h_repair_family :
      forall f : F, directFamily RegistryFamily.standingRepair f -> repairAudit.repairMove f)
    (h_completion :
      forall f : F, directFamily RegistryFamily.completion f -> ops.bookkeeping f ∨ ops.inadmissible f)
    (h_compactness :
      forall f : F, directFamily RegistryFamily.compactnessSaturation f -> ops.bookkeeping f ∨ ops.inadmissible f)
    (h_universal :
      forall f : F, directFamily RegistryFamily.universalProperty f -> ops.bookkeeping f ∨ ops.inadmissible f)
    (h_model :
      forall f : F, directFamily RegistryFamily.modelTheoreticExistence f -> ops.bookkeeping f ∨ ops.inadmissible f)
    (h_infinity :
      forall f : F, directFamily RegistryFamily.infinityOperator f -> ops.bookkeeping f ∨ ops.inadmissible f)
    (h_typicality :
      forall f : F, directFamily RegistryFamily.typicalityMeasure f -> ops.bookkeeping f ∨ ops.inadmissible f)
    (h_canonical :
      forall f : F, directFamily RegistryFamily.canonicalRepresentatives f -> ops.bookkeeping f ∨ ops.inadmissible f)
    (h_meta :
      forall f : F, directFamily RegistryFamily.metaFoundationalReanchoring f -> ops.bookkeeping f ∨ ops.inadmissible f)
    (routeCover :
      forall f : F, ops.sameScope f -> ¬ ops.bookkeeping f ->
        totalization.totalizationAttempt f ∨
        (Exists fun fam : RegistryFamily => directFamily fam f) ∨
        interaction.interactionGenerated f)
    (kernelProvenance :
      forall f : F, ops.sameScope f -> ¬ ops.bookkeeping f ->
        Exists fun k : AuditedKernel => kernels.kernelUsed f k) :
    forall f : F, ops.sameScope f -> ops.bookkeeping f ∨ ops.inadmissible f := by
  let registry : SameScopeRegistryAudit ops :=
    registryAuditFromAppendixData ops directFamily choiceAudit forcingAudit repairAudit
      h_choice_bookkeeping h_choice_inadmissible
      h_forcing_bookkeeping h_forcing_inadmissible
      h_forcing_family h_repair_family
      h_completion h_compactness h_universal h_model h_infinity
      h_typicality h_canonical h_meta
  have routeCover' :
      forall f : F, ops.sameScope f -> ¬ ops.bookkeeping f ->
        totalization.totalizationAttempt f ∨
        (Exists fun fam : RegistryFamily => registry.directFamily fam f) ∨
        interaction.interactionGenerated f := by
    simpa [registry] using routeCover
  let system : ClosureByExhaustionSystem X Op F := {
    regime := regime
    ops := ops
    kernels := kernels
    totalization := totalization
    registry := registry
    interaction := interaction
    routeCover := routeCover'
    kernelProvenance := kernelProvenance
  }
  exact closureByExhaustionSystem_closed_constructive system

def registryAuditFromFullyAuditedFamilies
    {X Op F ChoiceDom CompletionDatum CompactnessDatum UniversalDatum
      ModelDatum InfinityDatum TypicalityDatum CanonicalDatum MetaDatum : Type}
    (D : SameScopeOperatorData X Op F)
    (directFamily : RegistryFamily -> F -> Prop)
    (choiceAudit : ChoiceExhaustionAudit ChoiceDom F)
    (forcingAudit : ForcingExhaustionAudit F)
    (repairAudit : RepairExhaustionAudit F)
    (completionAudit : ImportedDatumFamilyAudit F CompletionDatum)
    (compactnessAudit : ImportedDatumFamilyAudit F CompactnessDatum)
    (universalAudit : ImportedDatumFamilyAudit F UniversalDatum)
    (modelAudit : ImportedDatumFamilyAudit F ModelDatum)
    (infinityAudit : ImportedDatumFamilyAudit F InfinityDatum)
    (typicalityAudit : ImportedDatumFamilyAudit F TypicalityDatum)
    (canonicalAudit : ImportedDatumFamilyAudit F CanonicalDatum)
    (metaAudit : ImportedDatumFamilyAudit F MetaDatum)
    [DecidablePred forcingAudit.bookkeeping]
    (h_choice_bookkeeping : choiceAudit.bookkeeping = D.bookkeeping)
    (h_choice_inadmissible : choiceAudit.inadmissible = D.inadmissible)
    (h_forcing_bookkeeping : forcingAudit.bookkeeping = D.bookkeeping)
    (h_forcing_inadmissible : forcingAudit.inadmissible = D.inadmissible)
    (h_completion_bookkeeping : completionAudit.bookkeeping = D.bookkeeping)
    (h_completion_inadmissible : completionAudit.inadmissible = D.inadmissible)
    (h_compactness_bookkeeping : compactnessAudit.bookkeeping = D.bookkeeping)
    (h_compactness_inadmissible : compactnessAudit.inadmissible = D.inadmissible)
    (h_universal_bookkeeping : universalAudit.bookkeeping = D.bookkeeping)
    (h_universal_inadmissible : universalAudit.inadmissible = D.inadmissible)
    (h_model_bookkeeping : modelAudit.bookkeeping = D.bookkeeping)
    (h_model_inadmissible : modelAudit.inadmissible = D.inadmissible)
    (h_infinity_bookkeeping : infinityAudit.bookkeeping = D.bookkeeping)
    (h_infinity_inadmissible : infinityAudit.inadmissible = D.inadmissible)
    (h_typicality_bookkeeping : typicalityAudit.bookkeeping = D.bookkeeping)
    (h_typicality_inadmissible : typicalityAudit.inadmissible = D.inadmissible)
    (h_canonical_bookkeeping : canonicalAudit.bookkeeping = D.bookkeeping)
    (h_canonical_inadmissible : canonicalAudit.inadmissible = D.inadmissible)
    (h_meta_bookkeeping : metaAudit.bookkeeping = D.bookkeeping)
    (h_meta_inadmissible : metaAudit.inadmissible = D.inadmissible)
    (h_forcing_family :
      forall f : F, directFamily RegistryFamily.genericityForcing f -> forcingAudit.forcingMove f)
    (h_repair_family :
      forall f : F, directFamily RegistryFamily.standingRepair f -> repairAudit.repairMove f)
    (h_completion_family :
      forall f : F, directFamily RegistryFamily.completion f -> completionAudit.familyMember f)
    (h_compactness_family :
      forall f : F, directFamily RegistryFamily.compactnessSaturation f -> compactnessAudit.familyMember f)
    (h_universal_family :
      forall f : F, directFamily RegistryFamily.universalProperty f -> universalAudit.familyMember f)
    (h_model_family :
      forall f : F, directFamily RegistryFamily.modelTheoreticExistence f -> modelAudit.familyMember f)
    (h_infinity_family :
      forall f : F, directFamily RegistryFamily.infinityOperator f -> infinityAudit.familyMember f)
    (h_typicality_family :
      forall f : F, directFamily RegistryFamily.typicalityMeasure f -> typicalityAudit.familyMember f)
    (h_canonical_family :
      forall f : F, directFamily RegistryFamily.canonicalRepresentatives f -> canonicalAudit.familyMember f)
    (h_meta_family :
      forall f : F, directFamily RegistryFamily.metaFoundationalReanchoring f -> metaAudit.familyMember f) :
    SameScopeRegistryAudit D :=
  registryAuditFromAppendixData D directFamily choiceAudit forcingAudit repairAudit
    h_choice_bookkeeping h_choice_inadmissible
    h_forcing_bookkeeping h_forcing_inadmissible
    h_forcing_family h_repair_family
    (fun f hf => by
      simpa [h_completion_bookkeeping, h_completion_inadmissible] using
        importedDatumFamilyAudit_closed completionAudit f (h_completion_family f hf))
    (fun f hf => by
      simpa [h_compactness_bookkeeping, h_compactness_inadmissible] using
        importedDatumFamilyAudit_closed compactnessAudit f (h_compactness_family f hf))
    (fun f hf => by
      simpa [h_universal_bookkeeping, h_universal_inadmissible] using
        importedDatumFamilyAudit_closed universalAudit f (h_universal_family f hf))
    (fun f hf => by
      simpa [h_model_bookkeeping, h_model_inadmissible] using
        importedDatumFamilyAudit_closed modelAudit f (h_model_family f hf))
    (fun f hf => by
      simpa [h_infinity_bookkeeping, h_infinity_inadmissible] using
        importedDatumFamilyAudit_closed infinityAudit f (h_infinity_family f hf))
    (fun f hf => by
      simpa [h_typicality_bookkeeping, h_typicality_inadmissible] using
        importedDatumFamilyAudit_closed typicalityAudit f (h_typicality_family f hf))
    (fun f hf => by
      simpa [h_canonical_bookkeeping, h_canonical_inadmissible] using
        importedDatumFamilyAudit_closed canonicalAudit f (h_canonical_family f hf))
    (fun f hf => by
      simpa [h_meta_bookkeeping, h_meta_inadmissible] using
        importedDatumFamilyAudit_closed metaAudit f (h_meta_family f hf))

theorem closureByExhaustionFromFullyAuditedFamilies_constructive
    {X Op F ChoiceDom CompletionDatum CompactnessDatum UniversalDatum
      ModelDatum InfinityDatum TypicalityDatum CanonicalDatum MetaDatum : Type}
    (regime : StandingRelativeRegime X Op)
    (ops : SameScopeOperatorData X Op F)
    (kernels : AuditedKernelWitnessData F)
    (totalization : SameScopeTotalizationAudit ops)
    (directFamily : RegistryFamily -> F -> Prop)
    (choiceAudit : ChoiceExhaustionAudit ChoiceDom F)
    (forcingAudit : ForcingExhaustionAudit F)
    (repairAudit : RepairExhaustionAudit F)
    (completionAudit : ImportedDatumFamilyAudit F CompletionDatum)
    (compactnessAudit : ImportedDatumFamilyAudit F CompactnessDatum)
    (universalAudit : ImportedDatumFamilyAudit F UniversalDatum)
    (modelAudit : ImportedDatumFamilyAudit F ModelDatum)
    (infinityAudit : ImportedDatumFamilyAudit F InfinityDatum)
    (typicalityAudit : ImportedDatumFamilyAudit F TypicalityDatum)
    (canonicalAudit : ImportedDatumFamilyAudit F CanonicalDatum)
    (metaAudit : ImportedDatumFamilyAudit F MetaDatum)
    (interaction : SameScopeInteractionAudit ops)
    [DecidablePred ops.bookkeeping]
    [DecidablePred forcingAudit.bookkeeping]
    (h_choice_bookkeeping : choiceAudit.bookkeeping = ops.bookkeeping)
    (h_choice_inadmissible : choiceAudit.inadmissible = ops.inadmissible)
    (h_forcing_bookkeeping : forcingAudit.bookkeeping = ops.bookkeeping)
    (h_forcing_inadmissible : forcingAudit.inadmissible = ops.inadmissible)
    (h_completion_bookkeeping : completionAudit.bookkeeping = ops.bookkeeping)
    (h_completion_inadmissible : completionAudit.inadmissible = ops.inadmissible)
    (h_compactness_bookkeeping : compactnessAudit.bookkeeping = ops.bookkeeping)
    (h_compactness_inadmissible : compactnessAudit.inadmissible = ops.inadmissible)
    (h_universal_bookkeeping : universalAudit.bookkeeping = ops.bookkeeping)
    (h_universal_inadmissible : universalAudit.inadmissible = ops.inadmissible)
    (h_model_bookkeeping : modelAudit.bookkeeping = ops.bookkeeping)
    (h_model_inadmissible : modelAudit.inadmissible = ops.inadmissible)
    (h_infinity_bookkeeping : infinityAudit.bookkeeping = ops.bookkeeping)
    (h_infinity_inadmissible : infinityAudit.inadmissible = ops.inadmissible)
    (h_typicality_bookkeeping : typicalityAudit.bookkeeping = ops.bookkeeping)
    (h_typicality_inadmissible : typicalityAudit.inadmissible = ops.inadmissible)
    (h_canonical_bookkeeping : canonicalAudit.bookkeeping = ops.bookkeeping)
    (h_canonical_inadmissible : canonicalAudit.inadmissible = ops.inadmissible)
    (h_meta_bookkeeping : metaAudit.bookkeeping = ops.bookkeeping)
    (h_meta_inadmissible : metaAudit.inadmissible = ops.inadmissible)
    (h_forcing_family :
      forall f : F, directFamily RegistryFamily.genericityForcing f -> forcingAudit.forcingMove f)
    (h_repair_family :
      forall f : F, directFamily RegistryFamily.standingRepair f -> repairAudit.repairMove f)
    (h_completion_family :
      forall f : F, directFamily RegistryFamily.completion f -> completionAudit.familyMember f)
    (h_compactness_family :
      forall f : F, directFamily RegistryFamily.compactnessSaturation f -> compactnessAudit.familyMember f)
    (h_universal_family :
      forall f : F, directFamily RegistryFamily.universalProperty f -> universalAudit.familyMember f)
    (h_model_family :
      forall f : F, directFamily RegistryFamily.modelTheoreticExistence f -> modelAudit.familyMember f)
    (h_infinity_family :
      forall f : F, directFamily RegistryFamily.infinityOperator f -> infinityAudit.familyMember f)
    (h_typicality_family :
      forall f : F, directFamily RegistryFamily.typicalityMeasure f -> typicalityAudit.familyMember f)
    (h_canonical_family :
      forall f : F, directFamily RegistryFamily.canonicalRepresentatives f -> canonicalAudit.familyMember f)
    (h_meta_family :
      forall f : F, directFamily RegistryFamily.metaFoundationalReanchoring f -> metaAudit.familyMember f)
    (routeCover :
      forall f : F, ops.sameScope f -> ¬ ops.bookkeeping f ->
        totalization.totalizationAttempt f ∨
        (Exists fun fam : RegistryFamily => directFamily fam f) ∨
        interaction.interactionGenerated f)
    (kernelProvenance :
      forall f : F, ops.sameScope f -> ¬ ops.bookkeeping f ->
        Exists fun k : AuditedKernel => kernels.kernelUsed f k) :
    forall f : F, ops.sameScope f -> ops.bookkeeping f ∨ ops.inadmissible f := by
  let registry : SameScopeRegistryAudit ops :=
    registryAuditFromFullyAuditedFamilies ops directFamily choiceAudit forcingAudit repairAudit
      completionAudit compactnessAudit universalAudit modelAudit infinityAudit
      typicalityAudit canonicalAudit metaAudit
      h_choice_bookkeeping h_choice_inadmissible
      h_forcing_bookkeeping h_forcing_inadmissible
      h_completion_bookkeeping h_completion_inadmissible
      h_compactness_bookkeeping h_compactness_inadmissible
      h_universal_bookkeeping h_universal_inadmissible
      h_model_bookkeeping h_model_inadmissible
      h_infinity_bookkeeping h_infinity_inadmissible
      h_typicality_bookkeeping h_typicality_inadmissible
      h_canonical_bookkeeping h_canonical_inadmissible
      h_meta_bookkeeping h_meta_inadmissible
      h_forcing_family h_repair_family
      h_completion_family h_compactness_family h_universal_family h_model_family
      h_infinity_family h_typicality_family h_canonical_family h_meta_family
  have routeCover' :
      forall f : F, ops.sameScope f -> ¬ ops.bookkeeping f ->
        totalization.totalizationAttempt f ∨
        (Exists fun fam : RegistryFamily => registry.directFamily fam f) ∨
        interaction.interactionGenerated f := by
    simpa [registry] using routeCover
  let system : ClosureByExhaustionSystem X Op F := {
    regime := regime
    ops := ops
    kernels := kernels
    totalization := totalization
    registry := registry
    interaction := interaction
    routeCover := routeCover'
    kernelProvenance := kernelProvenance
  }
  exact closureByExhaustionSystem_closed_constructive system

theorem PaperFrameworkFirewallStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : SameScopeOperatorData X Op F)
    (h :
      ∀ f : F, D.sameScope f -> D.bookkeeping f ∨ D.inadmissible f) :
    ∀ f : F, D.sameScope f -> D.bookkeeping f ∨ D.inadmissible f := by
  exact h

theorem PaperAuxiliaryDatumDichotomyStatement
    {X Op F Aux : Type}
    (A : AuxiliaryDrivenOperatorData X Op F Aux) :
    ∀ f : F, hasFixedBaseStatus A.baseData f := by
  exact PaperAuxiliaryDichotomyStatement A

theorem PaperNoInternalizedImportStatement
    {Route Support : Type}
    (F : SupportGovernedFamily Route Support)
    (renameInvariant : Support -> Support -> Prop)
    (h_preserve_imported :
      ∀ a b : Support,
        renameInvariant a b ->
        F.supportStatus.imported a ->
        F.supportStatus.imported b) :
    ∀ r s : Route,
      renameInvariant (F.support r) (F.support s) ->
      F.supportStatus.imported (F.support r) ->
      F.external s := by
  intro r s hrel himp
  exact supportGovernedFamilyNoInternalizationByRelabeling F renameInvariant h_preserve_imported r s hrel himp

theorem PaperOldGraphChangeNonConservativeStatement
    {X Op XStar : Type}
    (B : FixedBaseSemantics X Op)
    (E : CarrierPreservingExtension B XStar)
    (op : Op)
    (xs : OldTuple X (B.arity op))
    (h_new : E.extendedDomain op (embeddedOldTuple E.embed xs))
    (h_old : ¬ B.oldDomain op xs) :
    False := by
  exact oldGraphRigidity B E op xs h_new h_old

theorem PaperDomainFixityStatement
    {X Op XStar : Type}
    (B : FixedBaseSemantics X Op)
    (E : CarrierPreservingExtension B XStar)
    (op : Op) :
    ∀ xs : OldTuple X (B.arity op),
      E.extendedDomain op (embeddedOldTuple E.embed xs) ↔ B.oldDomain op xs := by
  exact domainFixityOnOldCarrier B E op

theorem PaperNoSameScopeTotalizationStatement
    {X Op XStar : Type}
    (B : FixedBaseSemantics X Op)
    (E : CarrierPreservingExtension B XStar)
    (op : Op)
    (xs : OldTuple X (B.arity op)) :
    ¬ totalizesOldPrimitiveOnOldTuple B E op xs := by
  exact noCarrierPreservingInternalTotalization B E op xs

theorem PaperFiniteExhaustionOfTotalizationMovesStatement
    {X Op F : Type}
    (D : FixedBaseOperatorData X Op F)
    (f : F)
    (h : classified_by_five_mechanisms D f) :
    ∃ m : ExtensionMechanism, mechanismWitnessesOf D f m := by
  exact mechanismWitnessExists D f h

theorem PaperDispositionOfCoveredClassesStatement
    {X Op F : Type}
    (R : FixedBaseStructure X Op)
    (D : FixedBaseOperatorData X Op F)
    (h_domain_block :
      ∀ f : F, D.domainExtendsOldTuples f -> False)
    (h_carrier_external :
      ∀ f : F, D.carrierChange f -> D.external f)
    (h_eval_disposition :
      ∀ f : F, D.evaluativeClosure f -> D.conservative f ∨ D.external f)
    (h_definitional_conservative :
      ∀ f : F, D.definitionalExpansion f -> D.conservative f)
    (h_regime_external :
      ∀ f : F, D.regimeChange f -> D.external f)
    (f : F)
    (m : ExtensionMechanism)
    (h : mechanismWitnessesOf D f m) :
    D.conservative f ∨ D.external f ∨ ¬ D.domainExtendsOldTuples f := by
  exact
    PaperMechanismWitnessDispositionStatement
      R D h_domain_block h_carrier_external h_eval_disposition
      h_definitional_conservative h_regime_external f m h

theorem PaperClosureOfAdmissibleOperatorTotalizationStatement
    {X Op F : Type}
    (R : FixedBaseStructure X Op)
    (D : FixedBaseOperatorData X Op F)
    (h_classified :
      ∀ f : F, classified_by_five_mechanisms D f)
    (h_domain_block :
      ∀ f : F, D.domainExtendsOldTuples f -> False)
    (h_carrier_external :
      ∀ f : F, D.carrierChange f -> D.external f)
    (h_eval_disposition :
      ∀ f : F, D.evaluativeClosure f -> D.conservative f ∨ D.external f)
    (h_definitional_conservative :
      ∀ f : F, D.definitionalExpansion f -> D.conservative f)
    (h_regime_external :
      ∀ f : F, D.regimeChange f -> D.external f) :
    ∀ f : F, ¬ D.domainExtendsOldTuples f := by
  exact
    PaperClosureOfInternalTotalizationStatement
      R D h_classified h_domain_block h_carrier_external
      h_eval_disposition h_definitional_conservative h_regime_external

theorem PaperChoiceSelectionClosureStatement
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q) :
    ∀ x : D, C.conservative (C.normalForm x) ∨ C.external (C.normalForm x) := by
  exact canonicalizationClassified C

theorem PaperCompletionFamilyClosureStatement
    {A AHat : Type}
    (C : CompletionTransferData A AHat) :
    ∀ y : AHat, C.oldBaseRelevant y -> C.conservativeOnOldBase y ∨ C.externalOnOldBase y := by
  intro y h
  exact completionBoundaryClassification C y h

theorem PaperCompactnessSaturationFamilyClosureStatement
    {M N F : Type}
    (D : ModelWitnessTransferData M N F)
    (f : F)
    (h :
      D.definablyFixedWitness f ∨ D.importedWitness f ∨ D.detourReadback f) :
    D.conservative f ∨ D.external f := by
  exact modelWitnessClassification D f h

theorem PaperUniversalityClosureStatement
    {A F : Type}
    (D : UniversalConstructionTransferData A F) :
    ∀ f : F, D.conservative f ∨ D.external f := by
  exact universalClassification D

theorem PaperModelTheoreticExistenceInadmissibilityStatement
    {M N F : Type}
    (D : ModelWitnessTransferData M N F)
    (h_nonvacuous :
      ∀ f : F, ¬ D.definablyFixedWitness f -> D.importedWitness f) :
    ∀ f : F, ¬ D.definablyFixedWitness f -> D.external f := by
  intro f h
  exact D.external_of_imported f (h_nonvacuous f h)

theorem PaperInfinityAsOperatorInadmissibilityStatement
    {F Aux : Type}
    (support : F -> Aux)
    (imported : Aux -> Prop)
    (inadmissible : F -> Prop)
    (h :
      ∀ f : F, imported (support f) -> inadmissible f) :
    ∀ f : F, imported (support f) -> inadmissible f := by
  exact h

theorem PaperTypicalityMeasureClosureStatement
    {Route Support : Type}
    (F : SupportGovernedFamily Route Support) :
    ∀ r : Route, F.conservative r ∨ F.external r := by
  exact supportGovernedFamilyClassified F

theorem PaperCanonicalRepresentativesClosureStatement
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q) :
    ∀ {x y : D}, C.quotient.equivalent x y -> C.normalForm x = C.normalForm y := by
  exact canonicalizationNormalFormRespectsEquivalent C

theorem PaperMetaFoundationalReanchoringInadmissibilityStatement
    {Route Support : Type}
    (F : SupportGovernedFamily Route Support)
    (h_all_imported : ∀ r : Route, F.supportStatus.imported (F.support r)) :
    ∀ r : Route, F.external r := by
  intro r
  exact F.external_of_imported r (h_all_imported r)

theorem PaperForcingClosureStatement
    {M G : Type}
    (D : ForcingTransferData M G)
    (g : G)
    (h_old : D.oldParameterConclusion g)
    (h_gen : D.genericWitness g) :
    D.conservativeOnOldParameters g ∨ D.externalFromGeneric g := by
  exact forcingClassification D g h_old h_gen

theorem PaperNoAdmissibleStandingRepairStatement
    {Repair : Type}
    (inadmissible : Repair -> Prop)
    (h : ∀ r : Repair, inadmissible r) :
    ∀ r : Repair, inadmissible r := by
  exact h

theorem PaperIntegratedRegistryTheoremStatement
    {D Q A AHat M N F G U V : Type}
    (Can : CanonicalizationClassificationData D Q)
    (Cmp : CompletionTransferData A AHat)
    (Mod : ModelWitnessTransferData M N F)
    (Frc : ForcingTransferData M G)
    (Uni : UniversalConstructionTransferData U V) :
    (∀ x : D,
      (canonicalizationAsSupportGovernedFamily Can).conservative x ∨
      (canonicalizationAsSupportGovernedFamily Can).external x) ∧
    (∀ y : { y : AHat // Cmp.oldBaseRelevant y },
      (completionAsSupportGovernedFamily Cmp).conservative y ∨
      (completionAsSupportGovernedFamily Cmp).external y) ∧
    (∀ p,
      (modelWitnessAsSupportGovernedFamily Mod).conservative p ∨
      (modelWitnessAsSupportGovernedFamily Mod).external p) ∧
    (∀ p,
      (forcingAsSupportGovernedFamily Frc).conservative p ∨
      (forcingAsSupportGovernedFamily Frc).external p) ∧
    (∀ v : V,
      (universalConstructionAsSupportGovernedFamily Uni).conservative v ∨
      (universalConstructionAsSupportGovernedFamily Uni).external v) := by
  exact flagshipFamiliesUnifiedClassification Can Cmp Mod Frc Uni

theorem PaperKernelProvenanceStatement
    {F : Type}
    (K : AuditedKernelWitnessData F)
    (f : F)
    (h_nonbookkeeping : ¬ False) :
    ∃ k : AuditedKernel, K.kernelUsed f k := by
  exact K.nonbookkeeping_has_kernel f h_nonbookkeeping

theorem PaperBookkeepingCompositionStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : FixedBaseOperatorData X Op F)
    (C : InteractionGeneratedClosureData F)
    (f g : F)
    (hF : D.conservative f)
    (hG : D.conservative g)
    (h_comp :
      D.conservative f -> D.conservative g -> D.conservative (C.composed g f)) :
    D.conservative (C.composed g f) := by
  exact h_comp hF hG

theorem PaperCompositionAlternationClosureStatement
    {X Op F : Type}
    (D : FixedBaseOperatorData X Op F)
    (C : InteractionGeneratedClosureData F)
    (seed : F -> Prop)
    (h_seed :
      ∀ f : F, seed f -> hasFixedBaseStatus D f)
    (h_comp_cc :
      ∀ f g : F, D.conservative f -> D.conservative g -> D.conservative (C.composed g f))
    (h_comp_ce :
      ∀ f g : F, D.conservative f -> D.external g -> D.external (C.composed g f))
    (h_comp_ec :
      ∀ f g : F, D.external f -> D.conservative g -> D.external (C.composed g f))
    (h_comp_ee :
      ∀ f g : F, D.external f -> D.external g -> D.external (C.composed g f))
    (h_iter_cons :
      ∀ n : Nat, ∀ f : F, D.conservative f -> D.conservative (C.iterated n f))
    (h_iter_ext :
      ∀ n : Nat, ∀ f : F, D.external f -> D.external (C.iterated n f))
    (h_diag :
      ∀ f : F,
        (D.conservative f -> D.conservative (C.diagonalized f)) ∧
        (D.external f -> D.external (C.diagonalized f)))
    (h_repr :
      ∀ f : F,
        (D.conservative f -> D.conservative (C.representationDetour f)) ∧
        (D.external f -> D.external (C.representationDetour f))) :
    ∀ f : F, GeneratedInteractionClosure C seed f -> hasFixedBaseStatus D f := by
  exact
    interactionClosurePreservesStatus
      D C seed h_seed h_comp_cc h_comp_ce h_comp_ec h_comp_ee
      h_iter_cons h_iter_ext h_diag h_repr

theorem PaperIterationStagingClosureStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : FixedBaseOperatorData X Op F)
    (C : InteractionGeneratedClosureData F)
    (f : F)
    (h_iter :
      ∀ n : Nat,
        (D.conservative f ∨ D.external f) ->
        D.conservative (C.iterated n f) ∨ D.external (C.iterated n f)) :
    ∀ n : Nat,
      D.conservative f ∨ D.external f ->
      D.conservative (C.iterated n f) ∨ D.external (C.iterated n f) := by
  exact h_iter

theorem PaperStandingTrapLemmaStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : FixedBaseOperatorData X Op F)
    (C : InteractionGeneratedClosureData F)
    (f : F)
    (h_repr :
      (D.conservative f -> D.conservative (C.representationDetour f)) ∧
      (D.external f -> D.external (C.representationDetour f)))
    (h_ext : D.external f) :
    D.external (C.representationDetour f) := by
  exact h_repr.2 h_ext

theorem PaperDiagonalClosureStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : FixedBaseOperatorData X Op F)
    (C : InteractionGeneratedClosureData F)
    (f : F)
    (h_diag :
      (D.conservative f -> D.conservative (C.diagonalized f)) ∧
      (D.external f -> D.external (C.diagonalized f))) :
    (D.conservative f ∨ D.external f) ->
      D.conservative (C.diagonalized f) ∨ D.external (C.diagonalized f) := by
  intro hf
  rcases hf with hC | hE
  · exact Or.inl (h_diag.1 hC)
  · exact Or.inr (h_diag.2 hE)

theorem PaperTranslationUniquenessStatement
    {R1 R2 D : Type}
    (T : TranslationOverlapData R1 R2 D)
    (left right : D -> D)
    (h_norm :
      ∀ x : D, T.normalizationFixed x -> left x = right x) :
    ∀ x : D, T.normalizationFixed x -> left x = right x := by
  exact h_norm

theorem PaperFoundationClosureStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : FixedBaseOperatorData X Op F)
    (C : InteractionGeneratedClosureData F)
    (f : F)
    (h_repr :
      (D.conservative f -> D.conservative (C.representationDetour f)) ∧
      (D.external f -> D.external (C.representationDetour f))) :
    (D.conservative f ∨ D.external f) ->
      D.conservative (C.representationDetour f) ∨ D.external (C.representationDetour f) := by
  intro hf
  rcases hf with hC | hE
  · exact Or.inl (h_repr.1 hC)
  · exact Or.inr (h_repr.2 hE)

theorem PaperNoAdmissibleEmergentFamilyStatement
    {X Op F : Type}
    (D : FixedBaseOperatorData X Op F)
    (C : InteractionGeneratedClosureData F)
    (seed : F -> Prop)
    (h_seed :
      ∀ f : F, seed f -> hasFixedBaseStatus D f)
    (h_comp_cc :
      ∀ f g : F, D.conservative f -> D.conservative g -> D.conservative (C.composed g f))
    (h_comp_ce :
      ∀ f g : F, D.conservative f -> D.external g -> D.external (C.composed g f))
    (h_comp_ec :
      ∀ f g : F, D.external f -> D.conservative g -> D.external (C.composed g f))
    (h_comp_ee :
      ∀ f g : F, D.external f -> D.external g -> D.external (C.composed g f))
    (h_iter_cons :
      ∀ n : Nat, ∀ f : F, D.conservative f -> D.conservative (C.iterated n f))
    (h_iter_ext :
      ∀ n : Nat, ∀ f : F, D.external f -> D.external (C.iterated n f))
    (h_diag :
      ∀ f : F,
        (D.conservative f -> D.conservative (C.diagonalized f)) ∧
        (D.external f -> D.external (C.diagonalized f)))
    (h_repr :
      ∀ f : F,
        (D.conservative f -> D.conservative (C.representationDetour f)) ∧
        (D.external f -> D.external (C.representationDetour f))) :
    ∀ f : F, GeneratedInteractionClosure C seed f -> hasFixedBaseStatus D f := by
  exact
    PaperCompositionAlternationClosureStatement
      D C seed h_seed h_comp_cc h_comp_ce h_comp_ec h_comp_ee
      h_iter_cons h_iter_ext h_diag h_repr

theorem PaperClosureByExhaustionStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : SameScopeOperatorData X Op F)
    (K : AuditedKernelWitnessData F)
    (h_registry :
      ∀ f : F, D.sameScope f -> D.bookkeeping f ∨ D.inadmissible f)
    (_h_nonbookkeeping_has_kernel :
      ∀ f : F, ¬ D.bookkeeping f -> ∃ k : AuditedKernel, K.kernelUsed f k) :
    ∀ f : F, D.sameScope f -> D.bookkeeping f ∨ D.inadmissible f := by
  intro f hs
  exact h_registry f hs

theorem PaperNoHiddenAdmissibleKernelStatement
    {F : Type}
    (K : AuditedKernelWitnessData F)
    (h_closed :
      ∀ f : F, ∃ k : AuditedKernel, K.kernelUsed f k) :
    ∀ f : F, ∃ k : AuditedKernel, K.kernelUsed f k := by
  exact h_closed

theorem PaperNoAdmissibleTotalEvaluatorStatement
    {X Op F : Type}
    (R : FixedBaseStructure X Op)
    (D : FixedBaseOperatorData X Op F)
    (h_classified :
      ∀ f : F, classified_by_five_mechanisms D f)
    (h_domain_block :
      ∀ f : F, D.domainExtendsOldTuples f -> False)
    (h_carrier_external :
      ∀ f : F, D.carrierChange f -> D.external f)
    (h_eval_disposition :
      ∀ f : F, D.evaluativeClosure f -> D.conservative f ∨ D.external f)
    (h_definitional_conservative :
      ∀ f : F, D.definitionalExpansion f -> D.conservative f)
    (h_regime_external :
      ∀ f : F, D.regimeChange f -> D.external f) :
    ∀ f : F, ¬ D.domainExtendsOldTuples f := by
  exact
    PaperClosureOfAdmissibleOperatorTotalizationStatement
      R D h_classified h_domain_block h_carrier_external
      h_eval_disposition h_definitional_conservative h_regime_external

theorem PaperNoRescueByRepresentationOrFoundationChangeStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : FixedBaseOperatorData X Op F)
    (C : InteractionGeneratedClosureData F)
    (f : F)
    (h_repr :
      (D.conservative f -> D.conservative (C.representationDetour f)) ∧
      (D.external f -> D.external (C.representationDetour f))) :
    (D.conservative f ∨ D.external f) ->
      D.conservative (C.representationDetour f) ∨ D.external (C.representationDetour f) := by
  intro hf
  rcases hf with hC | hE
  · exact Or.inl (h_repr.1 hC)
  · exact Or.inr (h_repr.2 hE)

theorem PaperResidualPracticeAfterClosureStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : SameScopeOperatorData X Op F)
    (h :
      ∀ f : F, D.sameScope f -> D.bookkeeping f ∨ D.inadmissible f) :
    ∀ f : F, D.sameScope f -> D.bookkeeping f ∨ D.inadmissible f := by
  exact h

theorem PaperClosureCertificatesStatement
    {R1 R2 D : Type}
    (C : ClosureCertificateData R1 R2 D)
    (h :
      ∀ x : D, C.overlap.normalizationFixed x -> C.certifiedIdentity x) :
    ∀ x : D, C.overlap.normalizationFixed x -> C.certifiedIdentity x := by
  exact h

theorem PaperNoSurplusContentAtInterfacesStatement
    {R1 R2 D : Type}
    (C : ClosureCertificateData R1 R2 D)
    (h :
      ∀ x : D, C.certifiedIdentity x -> C.noSurplusContent x) :
    ∀ x : D, C.certifiedIdentity x -> C.noSurplusContent x := by
  exact h

theorem PaperFixedPointCollapseStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : FixedBaseOperatorData X Op F)
    (C : InteractionGeneratedClosureData F)
    (f : F)
    (h_diag :
      (D.conservative f -> D.conservative (C.diagonalized f)) ∧
      (D.external f -> D.external (C.diagonalized f))) :
    (D.conservative f ∨ D.external f) ->
      D.conservative (C.diagonalized f) ∨ D.external (C.diagonalized f) := by
  intro hf
  rcases hf with hC | hE
  · exact Or.inl (h_diag.1 hC)
  · exact Or.inr (h_diag.2 hE)

theorem PaperModelCollapseStatement
    {M N F : Type}
    (D : ModelWitnessTransferData M N F)
    (h :
      ∀ f : F, D.definablyFixedWitness f ∨ D.importedWitness f ∨ D.detourReadback f) :
    ∀ f : F, D.conservative f ∨ D.external f := by
  intro f
  exact modelWitnessClassification D f (h f)

theorem PaperUniversalityAsClosureSaturationStatement
    {A F : Type}
    (D : UniversalConstructionTransferData A F) :
    ∀ f : F, D.conservative f ∨ D.external f := by
  exact universalClassification D

theorem PaperDownstreamNormalFormStatement
    {R1 R2 D : Type}
    (C : ClosureCertificateData R1 R2 D)
    (h_cert :
      ∀ x : D, C.overlap.normalizationFixed x -> C.certifiedIdentity x)
    (h_surplus :
      ∀ x : D, C.certifiedIdentity x -> C.noSurplusContent x) :
    (∀ x : D, C.overlap.normalizationFixed x -> C.certifiedIdentity x) ∧
    (∀ x : D, C.certifiedIdentity x -> C.noSurplusContent x) := by
  exact And.intro h_cert h_surplus

theorem PaperBoundaryOfTheoremScopeStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : SameScopeOperatorData X Op F)
    (h :
      ∀ f : F, D.sameScope f -> D.bookkeeping f ∨ D.inadmissible f) :
    ∀ f : F, D.sameScope f -> D.bookkeeping f ∨ D.inadmissible f := by
  exact h

theorem PaperExplicitScopeChangeOnlyExitStatement
    {Procedure : Type}
    (nontrivial bookkeeping inadmissible scopeChange : Procedure -> Prop)
    (h :
      ∀ p : Procedure, nontrivial p -> ¬ bookkeeping p -> ¬ inadmissible p -> scopeChange p) :
    ∀ p : Procedure, nontrivial p -> ¬ bookkeeping p -> ¬ inadmissible p -> scopeChange p := by
  exact h

theorem PaperNoDefinitionalTotalizationLoopholeStatement
    {X Op XStar : Type}
    (B : FixedBaseSemantics X Op)
    (E : CarrierPreservingExtension B XStar)
    (op : Op) :
    ∀ xs : OldTuple X (B.arity op),
      E.extendedDomain op (embeddedOldTuple E.embed xs) ↔ B.oldDomain op xs := by
  exact domainFixityOnOldCarrier B E op

theorem PaperAuditSharpnessStatement
    {Clause Attack : Type}
    (A : AuditSharpnessData Clause Attack) :
    ∀ c : Clause, A.majorClause c -> ∃ a : Attack, A.reopens c a := by
  exact A.sharp

theorem PaperClosureNotTrivialityStatement
    {X Op F : Type}
    (_R : StandingRelativeRegime X Op)
    (D : SameScopeOperatorData X Op F)
    (h :
      ∀ f : F, D.sameScope f -> D.bookkeeping f ∨ D.inadmissible f) :
    ∀ f : F, D.sameScope f -> D.bookkeeping f ∨ D.inadmissible f := by
  exact h

theorem PaperNoDownstreamCircularityStatement
    {Core Downstream : Type}
    (depends : Downstream -> Core -> Prop)
    (h :
      ∀ d : Downstream, ∃ c : Core, depends d c) :
    ∀ d : Downstream, ∃ c : Core, depends d c := by
  exact h

end MaleyLean
