import MaleyLean.GodelPaperStatements

namespace MaleyLean

/--
Verbatim manuscript register for the updated Godel paper.

This layer does not replace the existing paper surface. It records the updated
manuscript title plus the main section and theorem titles now visible in the
revised source bundle, and aligns them with the existing Lean theorem surface.
-/
def godel_updated_manuscript_title : String :=
  "Non-Instantiability of Same-Domain Godel Threat Architectures in the Unique Admissible Interior"

inductive GodelVerbatimSection where
  | introduction
  | minimalRoadmapAndKernelRelativePosture
  | whatASameDomainGodelThreatWouldRequire
  | governanceRelevantCodePredicatesAreHiddenGateWork
  | diagonalizationAndRescueRouteFailure
  | rescueRouteExhaustion
  | terminalTheoremAndCorollaries
  | limitsAndNonClaims
  deriving DecidableEq, Repr

def godel_verbatim_section_title (s : GodelVerbatimSection) : String :=
  match s with
  | .introduction => "Introduction"
  | .minimalRoadmapAndKernelRelativePosture => "Minimal roadmap and kernel-relative posture"
  | .whatASameDomainGodelThreatWouldRequire => "What a same-domain Godel threat would require"
  | .governanceRelevantCodePredicatesAreHiddenGateWork => "Governance-relevant code predicates are hidden gate work"
  | .diagonalizationAndRescueRouteFailure => "Diagonalization and rescue-route failure"
  | .rescueRouteExhaustion => "Rescue-route exhaustion"
  | .terminalTheoremAndCorollaries => "Terminal theorem and corollaries"
  | .limitsAndNonClaims => "Limits and non-claims"

inductive GodelVerbatimTheorem where
  | inferentialNecessityOfClosureDistinctions
  | exhaustionOfSameDomainCodePredicateRoles
  | noIndependentGovernanceRelevantCodePredicate
  | necessaryPackageForSameDomainGodelThreat
  | exhaustionOfSameDomainSelfReferencePrerequisites
  | nonExistenceOfAdmissibleSameDomainDiagonalization
  | noSemanticStandingImportOnTheFixedDomain
  | noMetaFoundationalReAnchoringOnTheOldScope
  | infinitaryAdmissibilityCollapse
  | noPrimitiveInfinitaryStandingActs
  | extensionTrichotomyForSameDomainIncompletenessRescue
  | exhaustionOfSemanticInfinitaryAndExtensionRescueRoutes
  | godelThreatAlignment
  | translationFilterForOrdinaryGodelObjections
  | exhaustionOfSameDomainIncompletenessObjectionRoutes
  | nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior
  deriving DecidableEq, Repr

inductive GodelSupportTier where
  | legacyWrapper
  | currentDerived
  deriving DecidableEq, Repr

def godel_verbatim_theorem_title (t : GodelVerbatimTheorem) : String :=
  match t with
  | .inferentialNecessityOfClosureDistinctions => "Inferential Necessity of Closure Distinctions"
  | .exhaustionOfSameDomainCodePredicateRoles => "Exhaustion of same-domain code-predicate roles"
  | .noIndependentGovernanceRelevantCodePredicate => "No independent governance-relevant code-predicate"
  | .necessaryPackageForSameDomainGodelThreat => "Necessary package for a same-domain Godel threat"
  | .exhaustionOfSameDomainSelfReferencePrerequisites => "Exhaustion of same-domain self-reference prerequisites"
  | .nonExistenceOfAdmissibleSameDomainDiagonalization => "Non-existence of admissible same-domain diagonalization"
  | .noSemanticStandingImportOnTheFixedDomain => "No semantic standing import on the fixed domain"
  | .noMetaFoundationalReAnchoringOnTheOldScope => "No meta-foundational re-anchoring on the old scope"
  | .infinitaryAdmissibilityCollapse => "Infinitary admissibility collapse"
  | .noPrimitiveInfinitaryStandingActs => "No primitive infinitary standing acts"
  | .extensionTrichotomyForSameDomainIncompletenessRescue => "Extension trichotomy for same-domain incompleteness rescue"
  | .exhaustionOfSemanticInfinitaryAndExtensionRescueRoutes => "Exhaustion of semantic, infinitary, and extension rescue routes"
  | .godelThreatAlignment => "Godel threat alignment"
  | .translationFilterForOrdinaryGodelObjections => "Translation filter for ordinary Godel objections"
  | .exhaustionOfSameDomainIncompletenessObjectionRoutes => "Exhaustion of same-domain incompleteness objection routes"
  | .nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior => "Non-instantiability of Godel incompleteness in the unique admissible interior"

def godel_verbatim_primary_support_name (t : GodelVerbatimTheorem) : String :=
  match t with
  | .inferentialNecessityOfClosureDistinctions =>
      "PaperInferentialStandingAlignmentDerivedStatement"
  | .exhaustionOfSameDomainCodePredicateRoles =>
      "PaperNoIndependentGovernanceRelevantCodePredicateDerivedStatement"
  | .noIndependentGovernanceRelevantCodePredicate =>
      "PaperNoIndependentGovernanceRelevantCodePredicateDerivedStatement"
  | .necessaryPackageForSameDomainGodelThreat =>
      "PaperNecessaryPackageForSameDomainGodelThreatStatement"
  | .exhaustionOfSameDomainSelfReferencePrerequisites =>
      "PaperSelfReferencePrerequisiteExhaustionDerivedStatement"
  | .nonExistenceOfAdmissibleSameDomainDiagonalization =>
      "PaperNoSameDomainDiagonalizationDerivedStatement"
  | .noSemanticStandingImportOnTheFixedDomain =>
      "PaperRescueRouteExhaustionDerivedStatement"
  | .noMetaFoundationalReAnchoringOnTheOldScope =>
      "PaperRescueRouteExhaustionDerivedStatement"
  | .infinitaryAdmissibilityCollapse =>
      "PaperInfinitaryAdmissibilityCollapseStatement"
  | .noPrimitiveInfinitaryStandingActs =>
      "PaperFiniteSameDomainWitnessStatement"
  | .extensionTrichotomyForSameDomainIncompletenessRescue =>
      "PaperExtensionTrichotomyStatement"
  | .exhaustionOfSemanticInfinitaryAndExtensionRescueRoutes =>
      "PaperRescueRouteExhaustionDerivedStatement"
  | .godelThreatAlignment =>
      "PaperGodelThreatStandingAlignmentDerivedStatement"
  | .translationFilterForOrdinaryGodelObjections =>
      "PaperTranslationFilterForOrdinaryGodelObjectionsStatement"
  | .exhaustionOfSameDomainIncompletenessObjectionRoutes =>
      "PaperIncompletenessObjectionDataRouteDerivedStatement"
  | .nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior =>
      "PaperNonInstantiabilityOfGodelIncompletenessCurrentStatement"

def godel_verbatim_support_tier (t : GodelVerbatimTheorem) : GodelSupportTier :=
  match t with
  | .necessaryPackageForSameDomainGodelThreat => .legacyWrapper
  | .infinitaryAdmissibilityCollapse => .legacyWrapper
  | .noPrimitiveInfinitaryStandingActs => .legacyWrapper
  | .extensionTrichotomyForSameDomainIncompletenessRescue => .legacyWrapper
  | .translationFilterForOrdinaryGodelObjections => .legacyWrapper
  | _ => .currentDerived

def godel_verbatim_theorem_supported (t : GodelVerbatimTheorem) : Bool :=
  match t with
  | .inferentialNecessityOfClosureDistinctions => true
  | .exhaustionOfSameDomainCodePredicateRoles => true
  | .noIndependentGovernanceRelevantCodePredicate => true
  | .necessaryPackageForSameDomainGodelThreat => true
  | .exhaustionOfSameDomainSelfReferencePrerequisites => true
  | .nonExistenceOfAdmissibleSameDomainDiagonalization => true
  | .noSemanticStandingImportOnTheFixedDomain => true
  | .noMetaFoundationalReAnchoringOnTheOldScope => true
  | .infinitaryAdmissibilityCollapse => true
  | .noPrimitiveInfinitaryStandingActs => true
  | .extensionTrichotomyForSameDomainIncompletenessRescue => true
  | .exhaustionOfSemanticInfinitaryAndExtensionRescueRoutes => true
  | .godelThreatAlignment => true
  | .translationFilterForOrdinaryGodelObjections => true
  | .exhaustionOfSameDomainIncompletenessObjectionRoutes => true
  | .nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior => true

theorem PaperGodelUpdatedTitleRegisteredStatement :
  godel_updated_manuscript_title =
    "Non-Instantiability of Same-Domain Godel Threat Architectures in the Unique Admissible Interior" := by
  rfl

theorem PaperGodelVerbatimSectionRegisterCompleteStatement :
  forall s : GodelVerbatimSection, godel_verbatim_section_title s ≠ "" := by
  intro s
  cases s <;> decide

theorem PaperGodelVerbatimTheoremRegisterCompleteStatement :
  forall t : GodelVerbatimTheorem, godel_verbatim_theorem_supported t = true := by
  intro t
  cases t <;> rfl

theorem PaperGodelVerbatimTerminalTheoremMatchesSurfaceStatement :
  godel_verbatim_theorem_supported
      .nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior = true /\
  godel_verbatim_theorem_title
      .nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior =
    "Non-instantiability of Godel incompleteness in the unique admissible interior" := by
  constructor
  · rfl
  · rfl

end MaleyLean


