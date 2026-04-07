namespace MaleyLean

/--
Lightweight fixed-base structure used for the paper
"Fixed-Base Exhaustion for Internal Operators".

This is intentionally a first-pass support surface: it captures the theorem
shapes the paper needs without pretending that the full case-study algebra
(forcing, saturation, completion, universal constructions, etc.) has already
been formalized in detail.
-/
structure FixedBaseStructure (X Op : Type) where
  oldDefined : Op → X → Prop
  nondegenerate : ∃ op : Op, ∃ x : X, ¬ oldDefined op x

/--
Five extension mechanisms from the manuscript's exhaustion section.
-/
inductive ExtensionMechanism where
  | domainExtension
  | carrierChange
  | evaluativeClosure
  | definitionalExpansion
  | regimeChange
deriving DecidableEq, Repr

/--
Abstract status of a purported carrier-preserving operator on a fixed base.
-/
structure FixedBaseOperatorData (X Op F : Type) where
  conservative : F → Prop
  external : F → Prop
  domainExtendsOldTuples : F → Prop
  carrierChange : F → Prop
  evaluativeClosure : F → Prop
  definitionalExpansion : F → Prop
  regimeChange : F → Prop

/--
Interaction-generated closure data for Section 8 of the math-closure paper.
-/
structure InteractionGeneratedClosureData (F : Type) where
  composed : F → F → F
  iterated : Nat → F → F
  diagonalized : F → F
  representationDetour : F → F

/--
Case-study data for canonicalization, selection, and quotienting.
-/
structure CanonicalizationData (X D : Type) where
  equivalent : D → D → Prop
  normalForm : D → D
  internallyFixedRule : D → Prop
  quotientPassage : D → Prop

/--
Case-study data for completion/evaluative closure.
-/
structure CompletionCaseData (A C : Type) where
  richerObject : C → A → Prop
  internallyFixedEvaluator : C → A → Prop
  externalEvaluator : C → A → Prop

/--
More detailed completion/readback data, matching the appendix decomposition:
enlargement plus readback.
-/
structure CompletionReadbackData (A AHat : Type) where
  embed : A → AHat
  oldBaseRelevant : AHat → Prop
  internallyFixedReadback : AHat → Prop
  conservativeReadback : AHat → Prop
  externalReadback : AHat → Prop

/--
Case-study data for compactness, saturation, and model-theoretic existence.
-/
structure ModelTheoryCaseData (M F : Type) where
  definablyFixedWitness : F → M → Prop
  externalWitnessImport : F → M → Prop

/--
Case-study data for forcing, genericity, and absoluteness.
-/
structure ForcingCaseData (M F : Type) where
  genericExtension : F → M → Prop
  conservativeReadback : F → M → Prop

/--
More detailed forcing/readback data, matching the appendix decomposition:
external extension plus absoluteness/invariance readback.
-/
structure ForcingReadbackData (M G : Type) where
  genericWitness : G → Prop
  oldParameterConclusion : G → Prop
  conservativeByReadback : G → Prop
  externalByGenericDependence : G → Prop

/--
Case-study data for universal constructions.
-/
structure UniversalConstructionCaseData (A F : Type) where
  internallyFixedWitness : F → A → Prop
  ambientExternalWitness : F → A → Prop

/--
Exhaustive mechanism classification.
-/
def classified_by_five_mechanisms
  {X Op F : Type}
  (D : FixedBaseOperatorData X Op F)
  (f : F) : Prop :=
  D.domainExtendsOldTuples f ∨
  D.carrierChange f ∨
  D.evaluativeClosure f ∨
  D.definitionalExpansion f ∨
  D.regimeChange f

/--
Paper-facing fixed-base rigidity statement.

If a purported carrier-preserving move would make an old undefined primitive
application defined on old data, then it is not an internal conservative move
on the fixed base.
-/
theorem PaperNoInternalTotalizationStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (h_block :
    ∀ f : F, D.domainExtendsOldTuples f → False) :
  ∀ f : F, ¬ D.domainExtendsOldTuples f := by
  intro f h
  exact h_block f h

/--
Paper-facing exhaustion theorem.

Every apparent internal strengthening falls under at least one of the five
mechanisms.
-/
theorem PaperExhaustionTheoremStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (h_classified :
    ∀ f : F, classified_by_five_mechanisms D f) :
  ∀ f : F, classified_by_five_mechanisms D f := by
  exact h_classified

/--
Disposition of the five mechanisms, in the paper's fixed-base form.

Each mechanism is either blocked or else reveals that no genuinely new internal
power has occurred.
-/
theorem PaperDispositionOfFiveMechanismsStatement
  {X Op F : Type}
  (B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (h_domain_block :
    ∀ f : F, D.domainExtendsOldTuples f → False)
  (h_carrier_external :
    ∀ f : F, D.carrierChange f → D.external f)
  (h_eval_disposition :
    ∀ f : F, D.evaluativeClosure f → D.conservative f ∨ D.external f)
  (h_definitional_conservative :
    ∀ f : F, D.definitionalExpansion f → D.conservative f)
  (h_regime_external :
    ∀ f : F, D.regimeChange f → D.external f) :
  ∀ f : F,
    classified_by_five_mechanisms D f →
    (D.conservative f ∨ D.external f ∨ ¬ D.domainExtendsOldTuples f) := by
  intro f hf
  rcases hf with hI | hII | hIII | hIV | hV
  · exact Or.inr (Or.inr (PaperNoInternalTotalizationStatement B D h_domain_block f))
  · exact Or.inr (Or.inl (h_carrier_external f hII))
  · rcases h_eval_disposition f hIII with hC | hE
    · exact Or.inl hC
    · exact Or.inr (Or.inl hE)
  · exact Or.inl (h_definitional_conservative f hIV)
  · exact Or.inr (Or.inl (h_regime_external f hV))

/--
Closure of internal totalization on the fixed base.
-/
theorem PaperClosureOfInternalTotalizationStatement
  {X Op F : Type}
  (B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (_h_classified :
    ∀ f : F, classified_by_five_mechanisms D f)
  (h_domain_block :
    ∀ f : F, D.domainExtendsOldTuples f → False)
  (_h_carrier_external :
    ∀ f : F, D.carrierChange f → D.external f)
  (_h_eval_disposition :
    ∀ f : F, D.evaluativeClosure f → D.conservative f ∨ D.external f)
  (_h_definitional_conservative :
    ∀ f : F, D.definitionalExpansion f → D.conservative f)
  (_h_regime_external :
    ∀ f : F, D.regimeChange f → D.external f) :
  ∀ f : F, ¬ D.domainExtendsOldTuples f := by
  intro f
  exact PaperNoInternalTotalizationStatement B D h_domain_block f

/--
Main paper-facing theorem.

Any purported carrier-preserving operator on the fixed base is either
conservative on old-base-relevant content or external; in particular, no such
operator totalizes an old genuinely partial operation on old tuples.
-/
theorem PaperNoNewInternalOperatorPowerStatement
  {X Op F : Type}
  (B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (h_classified :
    ∀ f : F, classified_by_five_mechanisms D f)
  (h_domain_block :
    ∀ f : F, D.domainExtendsOldTuples f → False)
  (h_carrier_external :
    ∀ f : F, D.carrierChange f → D.external f)
  (h_eval_disposition :
    ∀ f : F, D.evaluativeClosure f → D.conservative f ∨ D.external f)
  (h_definitional_conservative :
    ∀ f : F, D.definitionalExpansion f → D.conservative f)
  (h_regime_external :
    ∀ f : F, D.regimeChange f → D.external f) :
  ∀ f : F,
    (D.conservative f ∨ D.external f) ∧
    ¬ D.domainExtendsOldTuples f := by
  intro f
  constructor
  · rcases h_classified f with hI | hII | hIII | hIV | hV
    · exfalso
      exact h_domain_block f hI
    · exact Or.inr (h_carrier_external f hII)
    · exact h_eval_disposition f hIII
    · exact Or.inl (h_definitional_conservative f hIV)
    · exact Or.inr (h_regime_external f hV)
  · exact PaperNoInternalTotalizationStatement B D h_domain_block f

/--
Corollary-level no-internal-reentry principle.
-/
theorem PaperNoInternalReentryPrincipleStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (_h_classified :
    ∀ f : F, classified_by_five_mechanisms D f)
  (_h_domain_block :
    ∀ f : F, D.domainExtendsOldTuples f → False)
  (_h_carrier_external :
    ∀ f : F, D.carrierChange f → D.external f)
  (_h_eval_disposition :
    ∀ f : F, D.evaluativeClosure f → D.conservative f ∨ D.external f)
  (_h_definitional_conservative :
    ∀ f : F, D.definitionalExpansion f → D.conservative f)
  (_h_regime_external :
    ∀ f : F, D.regimeChange f → D.external f) :
  ∀ f : F, D.external f → ¬ (¬ D.conservative f ∧ ¬ D.external f) := by
  intro f hExt h
  exact h.2 hExt

/--
Section 8 lemma: conservative closure under composition.
-/
theorem PaperConservativeClosureUnderCompositionStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (C : InteractionGeneratedClosureData F)
  (f g : F)
  (hF : D.conservative f)
  (hG : D.conservative g)
  (h_comp :
    D.conservative f →
    D.conservative g →
    D.conservative (C.composed g f)) :
  D.conservative (C.composed g f) := by
  exact h_comp hF hG

/--
Section 8 theorem: composition and iteration do not create a third case.
-/
theorem PaperCompositionIterationNoThirdCaseStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (C : InteractionGeneratedClosureData F)
  (f : F)
  (h_iter :
    ∀ n : Nat,
      (D.conservative f ∨ D.external f) →
      D.conservative (C.iterated n f) ∨ D.external (C.iterated n f)) :
  ∀ n : Nat,
    D.conservative f ∨ D.external f →
    D.conservative (C.iterated n f) ∨ D.external (C.iterated n f) := by
  exact h_iter

/--
Section 8 proposition: diagonalization and fixed-point packaging.
-/
theorem PaperDiagonalizationPackagingStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (C : InteractionGeneratedClosureData F)
  (f : F)
  (h_diag :
    (D.conservative f → D.conservative (C.diagonalized f)) ∧
    (D.external f → D.external (C.diagonalized f))) :
  (D.conservative f ∨ D.external f) →
  D.conservative (C.diagonalized f) ∨ D.external (C.diagonalized f) := by
  intro hf
  rcases hf with hC | hE
  · exact Or.inl (h_diag.1 hC)
  · exact Or.inr (h_diag.2 hE)

/--
Section 8 proposition: representation change and foundation swap.
-/
theorem PaperRepresentationChangeStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (C : InteractionGeneratedClosureData F)
  (f : F)
  (h_repr :
    (D.conservative f → D.conservative (C.representationDetour f)) ∧
    (D.external f → D.external (C.representationDetour f))) :
  (D.conservative f ∨ D.external f) →
  D.conservative (C.representationDetour f) ∨ D.external (C.representationDetour f) := by
  intro hf
  rcases hf with hC | hE
  · exact Or.inl (h_repr.1 hC)
  · exact Or.inr (h_repr.2 hE)

/--
Section 8 theorem: no emergent family under interaction-generated closure.
-/
theorem PaperNoEmergentFamilyStatement
  {X Op F : Type}
  (B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (C : InteractionGeneratedClosureData F)
  (f : F)
  (h_base :
    D.conservative f ∨ D.external f)
  (h_diag :
    (D.conservative f → D.conservative (C.diagonalized f)) ∧
    (D.external f → D.external (C.diagonalized f)))
  (h_repr :
    (D.conservative f → D.conservative (C.representationDetour f)) ∧
    (D.external f → D.external (C.representationDetour f))) :
  (D.conservative (C.diagonalized f) ∨ D.external (C.diagonalized f)) ∧
  (D.conservative (C.representationDetour f) ∨
    D.external (C.representationDetour f)) := by
  constructor
  · exact PaperDiagonalizationPackagingStatement B D C f h_diag h_base
  · exact PaperRepresentationChangeStatement B D C f h_repr h_base

/--
Section 8 corollary: no internal re-entry by detour.
-/
theorem PaperNoInternalReentryByDetourStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (C : InteractionGeneratedClosureData F)
  (f : F)
  (h_repr :
    (D.conservative f → D.conservative (C.representationDetour f)) ∧
    (D.external f → D.external (C.representationDetour f)))
  (h_ext : D.external f) :
  D.external (C.representationDetour f) := by
  exact h_repr.2 h_ext

/--
Section 7 proposition: canonicalization, selection, and quotienting.
-/
theorem PaperCanonicalizationSelectionQuotientingStatement
  {X Op D : Type}
  (_B : FixedBaseStructure X Op)
  (C : CanonicalizationData X D)
  (h_cover :
    ∀ x : D,
      C.internallyFixedRule x ∨
      ¬ C.internallyFixedRule x ∨
      C.quotientPassage x) :
  ∀ x : D,
    C.internallyFixedRule x ∨
    ¬ C.internallyFixedRule x ∨
    C.quotientPassage x := by
  exact h_cover

/--
Section 7 proposition: completion and evaluative closure.
-/
theorem PaperCompletionEvaluativeClosureStatement
  {X Op A Cmpl : Type}
  (_B : FixedBaseStructure X Op)
  (C : CompletionCaseData A Cmpl)
  (c : Cmpl)
  (a : A) :
  C.richerObject c a ∨
  C.internallyFixedEvaluator c a ∨
  C.externalEvaluator c a →
  C.richerObject c a ∨
  C.internallyFixedEvaluator c a ∨
  C.externalEvaluator c a := by
  intro h
  exact h

/--
Section 7 proposition: compactness, saturation, and model-theoretic existence.
-/
theorem PaperModelTheoreticExistenceStatement
  {X Op M F : Type}
  (_B : FixedBaseStructure X Op)
  (D : ModelTheoryCaseData M F)
  (f : F)
  (m : M)
  (h_cover :
    D.definablyFixedWitness f m ∨ D.externalWitnessImport f m) :
  D.definablyFixedWitness f m ∨ D.externalWitnessImport f m := by
  exact h_cover

/--
Section 7 proposition: forcing, genericity, and absoluteness.
-/
theorem PaperForcingGenericityAbsolutenessStatement
  {X Op M F : Type}
  (_B : FixedBaseStructure X Op)
  (D : ForcingCaseData M F)
  (f : F)
  (m : M)
  (h_cover :
    D.genericExtension f m ∨ D.conservativeReadback f m) :
  D.genericExtension f m ∨ D.conservativeReadback f m := by
  exact h_cover

/--
Section 7 proposition: universal constructions and existence by universal
property.
-/
theorem PaperUniversalConstructionStatement
  {X Op A F : Type}
  (_B : FixedBaseStructure X Op)
  (D : UniversalConstructionCaseData A F)
  (f : F)
  (a : A)
  (h_cover :
    D.internallyFixedWitness f a ∨ D.ambientExternalWitness f a) :
  D.internallyFixedWitness f a ∨ D.ambientExternalWitness f a := by
  exact h_cover

/--
Section 7 theorem: flagship case-study closure.
-/
theorem PaperFlagshipCaseStudyClosureStatement
  {X Op Fam : Type}
  (_B : FixedBaseStructure X Op)
  (conservative external : Fam → Prop)
  (h_cover :
    ∀ f : Fam, conservative f ∨ external f) :
  ∀ f : Fam, conservative f ∨ external f := by
  exact h_cover

/--
Appendix case: completion decomposes into enlargement and readback.

If work in the richer ambient object is read back to old-base-relevant content
through an internally fixed readback, the old-base effect is conservative.
-/
theorem PaperCompletionReadbackConservativeStatement
  {X Op A AHat : Type}
  (_B : FixedBaseStructure X Op)
  (D : CompletionReadbackData A AHat)
  (y : AHat)
  (h_old : D.oldBaseRelevant y)
  (h_fixed : D.internallyFixedReadback y)
  (h_sound :
    ∀ z : AHat,
      D.oldBaseRelevant z →
      D.internallyFixedReadback z →
      D.conservativeReadback z) :
  D.conservativeReadback y := by
  exact h_sound y h_old h_fixed

/--
Appendix case: if the old-base readback still depends on an unfixed evaluator,
boundary convention, or comparison rule, the move remains external.
-/
theorem PaperCompletionReadbackExternalStatement
  {X Op A AHat : Type}
  (_B : FixedBaseStructure X Op)
  (D : CompletionReadbackData A AHat)
  (y : AHat)
  (h_old : D.oldBaseRelevant y)
  (h_ext :
    D.externalReadback y)
  (h_sound :
    ∀ z : AHat,
      D.oldBaseRelevant z →
      D.externalReadback z →
      D.externalReadback z) :
  D.externalReadback y := by
  exact h_sound y h_old h_ext

/--
Appendix case: forcing decomposes into witness import and readback.

The presence of the generic witness marks the forcing extension as external.
-/
theorem PaperForcingExtensionExternalStatement
  {X Op M G : Type}
  (_B : FixedBaseStructure X Op)
  (D : ForcingReadbackData M G)
  (g : G)
  (h_gen : D.genericWitness g)
  (h_sound :
    ∀ z : G, D.genericWitness z → D.externalByGenericDependence z) :
  D.externalByGenericDependence g := by
  exact h_sound g h_gen

/--
Appendix case: if the final conclusion concerns only old parameters and is
secured by readback, the effect on old-base-relevant content is conservative.
-/
theorem PaperForcingReadbackConservativeStatement
  {X Op M G : Type}
  (_B : FixedBaseStructure X Op)
  (D : ForcingReadbackData M G)
  (g : G)
  (h_old : D.oldParameterConclusion g)
  (h_sound :
    ∀ z : G, D.oldParameterConclusion z → D.conservativeByReadback z) :
  D.conservativeByReadback g := by
  exact h_sound g h_old

end MaleyLean
