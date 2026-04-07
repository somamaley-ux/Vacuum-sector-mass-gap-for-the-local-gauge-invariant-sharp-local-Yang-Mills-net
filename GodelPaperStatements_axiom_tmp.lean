import MaleyLean.PaperStatements
import MaleyLean.UniquenessPaperStatements
import MaleyLean.BivalentTrajectoryPaperStatements
import MaleyLean.EquivalenceExhaustionPaperStatements

namespace MaleyLean

/--
Same-domain roles a code-predicate may try to play in the paper's exhaustion
analysis.

This is a lightweight paper-facing classification surface: it records the role
partition used in the manuscript without pretending that the full coding and
diagonal machinery has already been formalized in detail.
-/
inductive CodePredicateRole where
  | inertBookkeeping
  | extensionalGateRenaming
  | sameSideRefinement
  | independentAuthorizer
deriving DecidableEq, Repr

/--
Route classes for same-domain incompleteness objections in the manuscript's
terminal route-exhaustion theorem.
-/
inductive IncompletenessRoute where
  | codeReadback
  | semanticImport
  | infinitaryImport
  | secondEquivalence
  | richerSameDomainExtension
  | explicitScopeChange
deriving DecidableEq, Repr

/--
Rescue-route classes used in the semantic/infinitary/extension exhaustion
section.
-/
inductive RescueRouteClass where
  | inertBookkeeping
  | extensionalGateRenaming
  | finiteWitnessCollapse
  | explicitScopeChange
  | inadmissibleAuthorityImport
deriving DecidableEq, Repr

/--
Paper-facing bridge for inferential necessity.

If a distinction threatens closure on the fixed domain, then it must survive
either at the standing-classification level or at the trajectory level.
-/
theorem PaperInferentialNecessityOfClosureDistinctionsStatement
  {A T Theta : Type}
  (_acts : A)
  (_trajs : T)
  (changesInferentialLife : Theta -> Prop)
  (changesStandingClassification : Theta -> Prop)
  (changesTrajectoryStructure : Theta -> Prop)
  (h_transmission :
    forall theta : Theta,
      changesInferentialLife theta ->
      changesStandingClassification theta \/
      changesTrajectoryStructure theta) :
  forall theta : Theta,
    changesInferentialLife theta ->
    changesStandingClassification theta \/
    changesTrajectoryStructure theta := by
  exact h_transmission

/--
Paper-facing exhaustion of same-domain code-predicate roles.
-/
theorem PaperCodePredicateRoleExhaustionStatement
  {P : Type}
  (roleOf : P -> CodePredicateRole)
  (h_exhaust :
    forall p : P,
      roleOf p = CodePredicateRole.inertBookkeeping \/
      roleOf p = CodePredicateRole.extensionalGateRenaming \/
      roleOf p = CodePredicateRole.sameSideRefinement \/
      roleOf p = CodePredicateRole.independentAuthorizer) :
  forall p : P,
    roleOf p = CodePredicateRole.inertBookkeeping \/
    roleOf p = CodePredicateRole.extensionalGateRenaming \/
    roleOf p = CodePredicateRole.sameSideRefinement \/
    roleOf p = CodePredicateRole.independentAuthorizer := by
  exact h_exhaust

/--
No independent governance-relevant code-predicate survives once same-side
refinement and independent authorizer branches are eliminated.
-/
theorem PaperNoIndependentGovernanceRelevantCodePredicateStatement
  {P : Type}
  (roleOf : P -> CodePredicateRole)
  (h_exhaust :
    forall p : P,
      roleOf p = CodePredicateRole.inertBookkeeping \/
      roleOf p = CodePredicateRole.extensionalGateRenaming \/
      roleOf p = CodePredicateRole.sameSideRefinement \/
      roleOf p = CodePredicateRole.independentAuthorizer)
  (h_no_refinement :
    forall p : P,
      roleOf p = CodePredicateRole.sameSideRefinement -> False)
  (h_no_independent :
    forall p : P,
      roleOf p = CodePredicateRole.independentAuthorizer -> False) :
  forall p : P,
    roleOf p = CodePredicateRole.inertBookkeeping \/
    roleOf p = CodePredicateRole.extensionalGateRenaming := by
  intro p
  rcases h_exhaust p with h_inert | h_gate | h_refine | h_indep
  · exact Or.inl h_inert
  · exact Or.inr h_gate
  · exact False.elim (h_no_refinement p h_refine)
  · exact False.elim (h_no_independent p h_indep)

/--
After code-role exhaustion, any remaining governance-relevant same-domain
self-reference candidate is gate-collapsed.
-/
theorem PaperSelfReferencePrerequisiteExhaustionStatement
  {P : Type}
  (roleOf : P -> CodePredicateRole)
  (governanceRelevant : P -> Prop)
  (gateCollapsedCandidate : P -> Prop)
  (h_exhaust :
    forall p : P,
      roleOf p = CodePredicateRole.inertBookkeeping \/
      roleOf p = CodePredicateRole.extensionalGateRenaming \/
      roleOf p = CodePredicateRole.sameSideRefinement \/
      roleOf p = CodePredicateRole.independentAuthorizer)
  (h_no_refinement :
    forall p : P,
      roleOf p = CodePredicateRole.sameSideRefinement -> False)
  (h_no_independent :
    forall p : P,
      roleOf p = CodePredicateRole.independentAuthorizer -> False)
  (h_gate_collapse :
    forall p : P,
      governanceRelevant p ->
      roleOf p = CodePredicateRole.extensionalGateRenaming ->
      gateCollapsedCandidate p)
  (h_inert_not_relevant :
    forall p : P,
      roleOf p = CodePredicateRole.inertBookkeeping ->
      governanceRelevant p ->
      False) :
  forall p : P,
    governanceRelevant p ->
    gateCollapsedCandidate p := by
  intro p hp
  rcases h_exhaust p with h_inert | h_gate | h_refine | h_indep
  · exact False.elim (h_inert_not_relevant p h_inert hp)
  · exact h_gate_collapse p hp h_gate
  · exact False.elim (h_no_refinement p h_refine)
  · exact False.elim (h_no_independent p h_indep)

/--
Paper-facing no-diagonalization theorem.

If every governance-relevant same-domain self-reference candidate collapses to a
gate-collapsed candidate, and such candidates are impossible, then no
governance-relevant same-domain diagonalization exists.
-/
theorem PaperNoSameDomainDiagonalizationStatement
  {G : Type}
  (governanceRelevant : G -> Prop)
  (gateCollapsedCandidate : G -> Prop)
  (h_collapse :
    forall g : G,
      governanceRelevant g ->
      gateCollapsedCandidate g)
  (h_gate_case_impossible :
    forall g : G,
      gateCollapsedCandidate g -> False) :
  forall g : G, governanceRelevant g -> False := by
  intro g hg
  exact h_gate_case_impossible g (h_collapse g hg)

/--
Semantic import on the old scope is exhausted by the standard classes used in
the paper.
-/
theorem PaperNoSemanticStandingImportStatement
  {R : Type}
  (classification : R -> RescueRouteClass)
  (h_classified :
    forall r : R,
      classification r = RescueRouteClass.inertBookkeeping \/
      classification r = RescueRouteClass.extensionalGateRenaming \/
      classification r = RescueRouteClass.explicitScopeChange \/
      classification r = RescueRouteClass.inadmissibleAuthorityImport) :
  forall r : R,
    classification r = RescueRouteClass.inertBookkeeping \/
    classification r = RescueRouteClass.extensionalGateRenaming \/
    classification r = RescueRouteClass.explicitScopeChange \/
    classification r = RescueRouteClass.inadmissibleAuthorityImport := by
  exact h_classified

/--
Infinitary same-domain force collapses to finite witness when it is genuinely
governance-relevant.
-/
theorem PaperInfinitaryAdmissibilityCollapseStatement
  {I W : Type}
  (governanceRelevant : I -> Prop)
  (hasFiniteWitness : I -> W -> Prop)
  (h_finite :
    forall i : I,
      governanceRelevant i ->
      exists w : W, hasFiniteWitness i w) :
  forall i : I,
    governanceRelevant i ->
    exists w : W, hasFiniteWitness i w := by
  exact h_finite

/--
Extension trichotomy in the paper's fixed-domain form.
-/
theorem PaperExtensionTrichotomyStatement
  {E : Type}
  (classification : E -> RescueRouteClass)
  (h_trichotomy :
    forall e : E,
      classification e = RescueRouteClass.inertBookkeeping \/
      classification e = RescueRouteClass.explicitScopeChange \/
      classification e = RescueRouteClass.inadmissibleAuthorityImport) :
  forall e : E,
    classification e = RescueRouteClass.inertBookkeeping \/
    classification e = RescueRouteClass.explicitScopeChange \/
    classification e = RescueRouteClass.inadmissibleAuthorityImport := by
  exact h_trichotomy

/--
Exhaustion of semantic, infinitary, and extension rescue routes.
-/
theorem PaperRescueRouteExhaustionStatement
  {R : Type}
  (classification : R -> RescueRouteClass)
  (h_exhaust :
    forall r : R,
      classification r = RescueRouteClass.inertBookkeeping \/
      classification r = RescueRouteClass.extensionalGateRenaming \/
      classification r = RescueRouteClass.finiteWitnessCollapse \/
      classification r = RescueRouteClass.explicitScopeChange \/
      classification r = RescueRouteClass.inadmissibleAuthorityImport) :
  forall r : R,
    classification r = RescueRouteClass.inertBookkeeping \/
    classification r = RescueRouteClass.extensionalGateRenaming \/
    classification r = RescueRouteClass.finiteWitnessCollapse \/
    classification r = RescueRouteClass.explicitScopeChange \/
    classification r = RescueRouteClass.inadmissibleAuthorityImport := by
  exact h_exhaust

/--
Terminal route-exhaustion theorem for same-domain incompleteness objections.
-/
theorem PaperIncompletenessObjectionRouteExhaustionStatement
  {O : Type}
  (routeOf : O -> IncompletenessRoute)
  (h_exhaust :
    forall o : O,
      routeOf o = IncompletenessRoute.codeReadback \/
      routeOf o = IncompletenessRoute.semanticImport \/
      routeOf o = IncompletenessRoute.infinitaryImport \/
      routeOf o = IncompletenessRoute.secondEquivalence \/
      routeOf o = IncompletenessRoute.richerSameDomainExtension \/
      routeOf o = IncompletenessRoute.explicitScopeChange)
  (h_no_code :
    forall o : O,
      routeOf o = IncompletenessRoute.codeReadback -> False)
  (h_no_semantic :
    forall o : O,
      routeOf o = IncompletenessRoute.semanticImport -> False)
  (h_no_infinitary :
    forall o : O,
      routeOf o = IncompletenessRoute.infinitaryImport -> False)
  (h_no_second_equivalence :
    forall o : O,
      routeOf o = IncompletenessRoute.secondEquivalence -> False)
  (h_no_extension :
    forall o : O,
      routeOf o = IncompletenessRoute.richerSameDomainExtension -> False) :
  forall o : O,
    routeOf o = IncompletenessRoute.explicitScopeChange := by
  intro o
  rcases h_exhaust o with h_code | h_sem | h_inf | h_eq | h_ext | h_scope
  · exact False.elim (h_no_code o h_code)
  · exact False.elim (h_no_semantic o h_sem)
  · exact False.elim (h_no_infinitary o h_inf)
  · exact False.elim (h_no_second_equivalence o h_eq)
  · exact False.elim (h_no_extension o h_ext)
  · exact h_scope

/--
Main paper-facing non-instantiability theorem.

If every same-domain incompleteness objection route collapses to explicit scope
change, then no same-domain Godel threat is instantiable in the admissible
interior.
-/
theorem PaperNonInstantiabilityOfGodelIncompletenessStatement
  {O : Type}
  (routeOf : O -> IncompletenessRoute)
  (sameDomainThreat : O -> Prop)
  (h_routes :
    forall o : O,
      routeOf o = IncompletenessRoute.explicitScopeChange)
  (h_same_domain_not_scope_change :
    forall o : O,
      sameDomainThreat o ->
      routeOf o = IncompletenessRoute.explicitScopeChange -> False) :
  forall o : O,
    sameDomainThreat o -> False := by
  intro o ho
  exact h_same_domain_not_scope_change o ho (h_routes o)

/--
Corollary surface for the paper's "true but unprovable" split claim.
-/
theorem PaperNoGovernanceRelevantTrueButUnprovableSplitStatement
  {A : Type}
  (split : A -> Prop)
  (standingLike : A -> Prop)
  (h_no_split :
    forall a : A,
      split a -> standingLike a)
  (h_no_second_side :
    forall a : A,
      standingLike a -> split a) :
  forall a : A, split a <-> standingLike a := by
  intro a
  constructor
  · intro ha
    exact h_no_split a ha
  · intro ha
    exact h_no_second_side a ha

/--
Corollary surface for stability of the unique admissible interior.
-/
theorem PaperStabilityOfUniqueAdmissibleInteriorStatement
  {alpha : Type}
  (S : System alpha)
  (I1 I2 : alpha -> Prop)
  (h1 : forall a, I1 a -> standing S a)
  (h2 : forall a, I2 a -> standing S a)
  (h_complete1 : forall a, standing S a -> I1 a)
  (h_complete2 : forall a, standing S a -> I2 a) :
  lawfully_equivalent_interiors I1 I2 := by
  exact
    PaperUniquenessOfAdmissibleInteriorCoreStatement
      S I1 I2 h1 h2 h_complete1 h_complete2

end MaleyLean

#print axioms MaleyLean.PaperInferentialNecessityOfClosureDistinctionsStatement
#print axioms MaleyLean.PaperCodePredicateRoleExhaustionStatement
#print axioms MaleyLean.PaperNoIndependentGovernanceRelevantCodePredicateStatement
#print axioms MaleyLean.PaperSelfReferencePrerequisiteExhaustionStatement
#print axioms MaleyLean.PaperNoSameDomainDiagonalizationStatement
#print axioms MaleyLean.PaperNoSemanticStandingImportStatement
#print axioms MaleyLean.PaperInfinitaryAdmissibilityCollapseStatement
#print axioms MaleyLean.PaperExtensionTrichotomyStatement
#print axioms MaleyLean.PaperRescueRouteExhaustionStatement
#print axioms MaleyLean.PaperIncompletenessObjectionRouteExhaustionStatement
#print axioms MaleyLean.PaperNonInstantiabilityOfGodelIncompletenessStatement
#print axioms MaleyLean.PaperNoGovernanceRelevantTrueButUnprovableSplitStatement
#print axioms MaleyLean.PaperStabilityOfUniqueAdmissibleInteriorStatement
