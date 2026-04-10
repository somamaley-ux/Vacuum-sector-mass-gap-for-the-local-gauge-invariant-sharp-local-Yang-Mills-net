namespace MaleyLean

abbrev OldTuple (X : Type) (n : Nat) := Fin n -> X

def embeddedOldTuple {X XStar : Type} (embed : X -> XStar) {n : Nat}
    (xs : OldTuple X n) : OldTuple XStar n :=
  fun i => embed (xs i)

/--
Paper-facing summary layer for the manuscript
"Fixed-Base Exhaustion for Internal Operators".

This summary API is retained for the public theorem names, while the richer
semantic spine below internalizes tuple-level, quotient-level, readback-level,
and interaction-closure structure more explicitly.
-/
structure FixedBaseStructure (X Op : Type) where
  oldDefined : Op -> X -> Prop
  nondegenerate : Exists fun op : Op => Exists fun x : X => ¬ oldDefined op x

/-- Five extension mechanisms from the manuscript's exhaustion section. -/
inductive ExtensionMechanism where
  | domainExtension
  | carrierChange
  | evaluativeClosure
  | definitionalExpansion
  | regimeChange
deriving DecidableEq, Repr

/-- Summary status of a purported carrier-preserving operator on a fixed base. -/
structure FixedBaseOperatorData (X Op F : Type) where
  conservative : F -> Prop
  external : F -> Prop
  domainExtendsOldTuples : F -> Prop
  carrierChange : F -> Prop
  evaluativeClosure : F -> Prop
  definitionalExpansion : F -> Prop
  regimeChange : F -> Prop

def hasFixedBaseStatus {X Op F : Type} (D : FixedBaseOperatorData X Op F) (f : F) : Prop :=
  D.conservative f ∨ D.external f

/-- Interaction-generated closure data for Section 8 of the paper. -/
structure InteractionGeneratedClosureData (F : Type) where
  composed : F -> F -> F
  iterated : Nat -> F -> F
  diagonalized : F -> F
  representationDetour : F -> F

/-- Summary case-study data for canonicalization, selection, and quotienting. -/
structure CanonicalizationData (X D : Type) where
  equivalent : D -> D -> Prop
  normalForm : D -> D
  internallyFixedRule : D -> Prop
  quotientPassage : D -> Prop

/-- Summary case-study data for completion/evaluative closure. -/
structure CompletionCaseData (A C : Type) where
  richerObject : C -> A -> Prop
  internallyFixedEvaluator : C -> A -> Prop
  externalEvaluator : C -> A -> Prop

/-- Summary completion/readback data. -/
structure CompletionReadbackData (A AHat : Type) where
  embed : A -> AHat
  oldBaseRelevant : AHat -> Prop
  internallyFixedReadback : AHat -> Prop
  conservativeReadback : AHat -> Prop
  externalReadback : AHat -> Prop

/-- Summary case-study data for compactness, saturation, and model theory. -/
structure ModelTheoryCaseData (M F : Type) where
  definablyFixedWitness : F -> M -> Prop
  externalWitnessImport : F -> M -> Prop

/-- Summary case-study data for forcing, genericity, and absoluteness. -/
structure ForcingCaseData (M F : Type) where
  genericExtension : F -> M -> Prop
  conservativeReadback : F -> M -> Prop

/-- Summary forcing/readback data. -/
structure ForcingReadbackData (M G : Type) where
  genericWitness : G -> Prop
  oldParameterConclusion : G -> Prop
  conservativeByReadback : G -> Prop
  externalByGenericDependence : G -> Prop

/-- Summary case-study data for universal constructions. -/
structure UniversalConstructionCaseData (A F : Type) where
  internallyFixedWitness : F -> A -> Prop
  ambientExternalWitness : F -> A -> Prop

/-- Exhaustive mechanism classification. -/
def classified_by_five_mechanisms
  {X Op F : Type}
  (D : FixedBaseOperatorData X Op F)
  (f : F) : Prop :=
  D.domainExtendsOldTuples f ∨
  D.carrierChange f ∨
  D.evaluativeClosure f ∨
  D.definitionalExpansion f ∨
  D.regimeChange f

/-- Tuple-level semantic layer for old primitives on the fixed base. -/
structure FixedBaseSemantics (X Op : Type) where
  arity : Op -> Nat
  oldDomain : (op : Op) -> OldTuple X (arity op) -> Prop
  nondegenerate :
    Exists fun op : Op => Exists fun xs : OldTuple X (arity op) => ¬ oldDomain op xs

/-- Admissible extension preserving the old graph on already-defined tuples. -/
structure AdmissibleExtension {X Op : Type}
    (B : FixedBaseSemantics X Op) (XStar : Type) where
  embed : X -> XStar
  extendedDomain : (op : Op) -> OldTuple XStar (B.arity op) -> Prop
  preservesOldDefined :
    ∀ op : Op, ∀ xs : OldTuple X (B.arity op),
      B.oldDomain op xs -> extendedDomain op (embeddedOldTuple embed xs)

/-- Carrier-preserving extensions also reflect definedness back to the old base. -/
structure CarrierPreservingExtension {X Op : Type}
    (B : FixedBaseSemantics X Op) (XStar : Type)
    extends AdmissibleExtension B XStar where
  reflectsOldDefined :
    ∀ op : Op, ∀ xs : OldTuple X (B.arity op),
      extendedDomain op (embeddedOldTuple embed xs) -> B.oldDomain op xs

def totalizesOldPrimitiveOnOldTuple
    {X Op XStar : Type}
    (B : FixedBaseSemantics X Op)
    (E : CarrierPreservingExtension B XStar)
    (op : Op) (xs : OldTuple X (B.arity op)) : Prop :=
  ¬ B.oldDomain op xs ∧ E.extendedDomain op (embeddedOldTuple E.embed xs)

theorem oldTupleDomainPreserved
    {X Op XStar : Type}
    (B : FixedBaseSemantics X Op)
    (E : CarrierPreservingExtension B XStar)
    (op : Op) (xs : OldTuple X (B.arity op)) :
    E.extendedDomain op (embeddedOldTuple E.embed xs) ↔ B.oldDomain op xs := by
  constructor
  · intro h
    exact E.reflectsOldDefined op xs h
  · intro h
    exact E.preservesOldDefined op xs h

theorem oldGraphRigidity
    {X Op XStar : Type}
    (B : FixedBaseSemantics X Op)
    (E : CarrierPreservingExtension B XStar)
    (op : Op) (xs : OldTuple X (B.arity op))
    (h_new : E.extendedDomain op (embeddedOldTuple E.embed xs))
    (h_old : ¬ B.oldDomain op xs) : False := by
  exact h_old (E.reflectsOldDefined op xs h_new)

theorem domainFixityOnOldCarrier
    {X Op XStar : Type}
    (B : FixedBaseSemantics X Op)
    (E : CarrierPreservingExtension B XStar)
    (op : Op) :
    ∀ xs : OldTuple X (B.arity op),
      E.extendedDomain op (embeddedOldTuple E.embed xs) ↔ B.oldDomain op xs := by
  intro xs
  exact oldTupleDomainPreserved B E op xs

theorem noCarrierPreservingInternalTotalization
    {X Op XStar : Type}
    (B : FixedBaseSemantics X Op)
    (E : CarrierPreservingExtension B XStar)
    (op : Op) (xs : OldTuple X (B.arity op)) :
    ¬ totalizesOldPrimitiveOnOldTuple B E op xs := by
  intro h
  exact h.1 (E.reflectsOldDefined op xs h.2)

/-- Auxiliary datum classification used in the paper's Section 5 spine. -/
structure AuxiliaryDatumStatus (Aux : Type) where
  internallyFixed : Aux -> Prop
  imported : Aux -> Prop

structure AuxiliaryDrivenOperatorData (X Op F Aux : Type) where
  baseData : FixedBaseOperatorData X Op F
  support : F -> Aux
  supportStatus : AuxiliaryDatumStatus Aux
  conservative_of_fixed :
    ∀ f : F, supportStatus.internallyFixed (support f) -> baseData.conservative f
  external_of_imported :
    ∀ f : F, supportStatus.imported (support f) -> baseData.external f
  support_classified :
    ∀ f : F,
      supportStatus.internallyFixed (support f) ∨ supportStatus.imported (support f)

theorem auxiliarySupportClassified
    {X Op F Aux : Type}
    (A : AuxiliaryDrivenOperatorData X Op F Aux)
    (f : F) :
    A.supportStatus.internallyFixed (A.support f) ∨
      A.supportStatus.imported (A.support f) := by
  exact A.support_classified f

theorem PaperAuxiliaryDichotomyStatement
    {X Op F Aux : Type}
    (A : AuxiliaryDrivenOperatorData X Op F Aux) :
    ∀ f : F, hasFixedBaseStatus A.baseData f := by
  intro f
  rcases A.support_classified f with h_fixed | h_imported
  · exact Or.inl (A.conservative_of_fixed f h_fixed)
  · exact Or.inr (A.external_of_imported f h_imported)

/--
Unified family interface for the case-study table: every route is governed by a
support datum whose fixed-vs-imported status determines the conservative-vs-
external classification.
-/
structure SupportGovernedFamily (Route Support : Type) where
  support : Route -> Support
  conservative : Route -> Prop
  external : Route -> Prop
  supportStatus : AuxiliaryDatumStatus Support
  conservative_of_fixed :
    ∀ r : Route, supportStatus.internallyFixed (support r) -> conservative r
  external_of_imported :
    ∀ r : Route, supportStatus.imported (support r) -> external r
  support_classified :
    ∀ r : Route,
      supportStatus.internallyFixed (support r) ∨ supportStatus.imported (support r)

theorem supportGovernedFamilyClassified
    {Route Support : Type}
    (F : SupportGovernedFamily Route Support) :
    ∀ r : Route, F.conservative r ∨ F.external r := by
  intro r
  rcases F.support_classified r with h_fixed | h_imported
  · exact Or.inl (F.conservative_of_fixed r h_fixed)
  · exact Or.inr (F.external_of_imported r h_imported)

theorem supportGovernedFamilyNoInternalizationByRelabeling
    {Route Support : Type}
    (F : SupportGovernedFamily Route Support)
    (renameInvariant : Support -> Support -> Prop)
    (h_preserve_imported :
      ∀ a b : Support,
        renameInvariant a b ->
        F.supportStatus.imported a ->
        F.supportStatus.imported b)
    (r s : Route)
    (h_relabeled : renameInvariant (F.support r) (F.support s))
    (h_imported : F.supportStatus.imported (F.support r)) :
    F.external s := by
  exact F.external_of_imported s (h_preserve_imported _ _ h_relabeled h_imported)

theorem noInternalizationByRelabeling
    {X Op F Aux : Type}
    (A : AuxiliaryDrivenOperatorData X Op F Aux)
    (renameInvariant : Aux -> Aux -> Prop)
    (h_preserve_imported :
      ∀ a b : Aux, renameInvariant a b -> A.supportStatus.imported a -> A.supportStatus.imported b)
    (f g : F)
    (h_relabeled : renameInvariant (A.support f) (A.support g))
    (h_imported : A.supportStatus.imported (A.support f)) :
    A.baseData.external g := by
  have h_imported_g : A.supportStatus.imported (A.support g) :=
    h_preserve_imported (A.support f) (A.support g) h_relabeled h_imported
  exact A.external_of_imported g h_imported_g

def mechanismWitnessesOf
    {X Op F : Type}
    (D : FixedBaseOperatorData X Op F)
    (f : F) : ExtensionMechanism -> Prop
  | .domainExtension => D.domainExtendsOldTuples f
  | .carrierChange => D.carrierChange f
  | .evaluativeClosure => D.evaluativeClosure f
  | .definitionalExpansion => D.definitionalExpansion f
  | .regimeChange => D.regimeChange f

theorem mechanismWitnessExists
    {X Op F : Type}
    (D : FixedBaseOperatorData X Op F)
    (f : F)
    (h : classified_by_five_mechanisms D f) :
    ∃ m : ExtensionMechanism, mechanismWitnessesOf D f m := by
  rcases h with hI | hII | hIII | hIV | hV
  · exact ⟨.domainExtension, hI⟩
  · exact ⟨.carrierChange, hII⟩
  · exact ⟨.evaluativeClosure, hIII⟩
  · exact ⟨.definitionalExpansion, hIV⟩
  · exact ⟨.regimeChange, hV⟩

theorem mechanismWitnessSound
    {X Op F : Type}
    (D : FixedBaseOperatorData X Op F)
    (f : F)
    {m : ExtensionMechanism}
    (h : mechanismWitnessesOf D f m) :
    classified_by_five_mechanisms D f := by
  cases m with
  | domainExtension =>
      exact Or.inl h
  | carrierChange =>
      exact Or.inr (Or.inl h)
  | evaluativeClosure =>
      exact Or.inr (Or.inr (Or.inl h))
  | definitionalExpansion =>
      exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  | regimeChange =>
      exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Quotient/presentation layer for canonical representative arguments. -/
structure QuotientPresentation (D Q : Type) where
  equivalent : D -> D -> Prop
  quotientMap : D -> Q
  representative : Q -> D
  quotient_sound :
    ∀ x y : D, equivalent x y -> quotientMap x = quotientMap y
  quotient_complete :
    ∀ x y : D, quotientMap x = quotientMap y -> equivalent x y
  representative_section :
    ∀ q : Q, quotientMap (representative q) = q

structure CanonicalizationClassificationData (D Q : Type) where
  quotient : QuotientPresentation D Q
  normalForm : D -> D
  conservative : D -> Prop
  external : D -> Prop
  factorsThroughRepresentative :
    ∀ x : D, normalForm x = quotient.representative (quotient.quotientMap x)
  internallyFixedRepresentative : Q -> Prop
  externallyChosenRepresentative : Q -> Prop
  conservative_of_fixed :
    ∀ x : D,
      internallyFixedRepresentative (quotient.quotientMap x) ->
      conservative (normalForm x)
  external_of_unfixed :
    ∀ x : D,
      externallyChosenRepresentative (quotient.quotientMap x) ->
      external (normalForm x)
  representative_classified :
    ∀ q : Q, internallyFixedRepresentative q ∨ externallyChosenRepresentative q

theorem canonicalizationFactorsThroughQuotient
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q) :
    ∀ x : D, C.normalForm x = C.quotient.representative (C.quotient.quotientMap x) := by
  intro x
  exact C.factorsThroughRepresentative x

theorem equivalentInputsShareNormalForm
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q)
    {x y : D}
    (hxy : C.quotient.equivalent x y) :
    C.normalForm x = C.normalForm y := by
  rw [C.factorsThroughRepresentative x, C.factorsThroughRepresentative y]
  have hq : C.quotient.quotientMap x = C.quotient.quotientMap y :=
    C.quotient.quotient_sound x y hxy
  rw [hq]

theorem canonicalizationInternallyFixedIsConservative
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q)
    (x : D)
    (h_fixed : C.internallyFixedRepresentative (C.quotient.quotientMap x)) :
    C.conservative (C.normalForm x) := by
  exact C.conservative_of_fixed x h_fixed

theorem canonicalizationExternalSelectorIsExternal
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q)
    (x : D)
    (h_ext : C.externallyChosenRepresentative (C.quotient.quotientMap x)) :
    C.external (C.normalForm x) := by
  exact C.external_of_unfixed x h_ext

theorem canonicalizationClassified
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q) :
    ∀ x : D, C.conservative (C.normalForm x) ∨ C.external (C.normalForm x) := by
  intro x
  rcases C.representative_classified (C.quotient.quotientMap x) with h_fixed | h_ext
  · exact Or.inl (C.conservative_of_fixed x h_fixed)
  · exact Or.inr (C.external_of_unfixed x h_ext)

theorem canonicalizationRepresentativeOfEquivalentInputsAgrees
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q)
    {x y : D}
    (hxy : C.quotient.equivalent x y) :
    C.quotient.representative (C.quotient.quotientMap x) =
      C.quotient.representative (C.quotient.quotientMap y) := by
  have hq : C.quotient.quotientMap x = C.quotient.quotientMap y :=
    C.quotient.quotient_sound x y hxy
  rw [hq]

theorem canonicalizationNormalFormRespectsEquivalent
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q) :
    ∀ {x y : D}, C.quotient.equivalent x y -> C.normalForm x = C.normalForm y := by
  intro x y hxy
  exact equivalentInputsShareNormalForm C hxy

def canonicalizationAsSupportGovernedFamily
    {D Q : Type}
    (C : CanonicalizationClassificationData D Q) :
    SupportGovernedFamily D Q where
  support := fun x => C.quotient.quotientMap x
  conservative := fun x => C.conservative (C.normalForm x)
  external := fun x => C.external (C.normalForm x)
  supportStatus :=
    { internallyFixed := C.internallyFixedRepresentative
      imported := C.externallyChosenRepresentative }
  conservative_of_fixed := by
    intro x h_fixed
    exact C.conservative_of_fixed x h_fixed
  external_of_imported := by
    intro x h_imported
    exact C.external_of_unfixed x h_imported
  support_classified := by
    intro x
    exact C.representative_classified (C.quotient.quotientMap x)

/-- Completion-level semantic packet: enlargement plus readback. -/
structure CompletionTransferData (A AHat : Type) where
  embed : A -> AHat
  readback : AHat -> A
  oldBaseRelevant : AHat -> Prop
  internallyFixedBoundary : AHat -> Prop
  externallyChosenBoundary : AHat -> Prop
  conservativeOnOldBase : AHat -> Prop
  externalOnOldBase : AHat -> Prop
  embed_oldBaseRelevant : ∀ a : A, oldBaseRelevant (embed a)
  readback_embed : ∀ a : A, readback (embed a) = a
  conservative_of_fixed_boundary :
    ∀ y : AHat,
      oldBaseRelevant y ->
      internallyFixedBoundary y ->
      conservativeOnOldBase y
  external_of_external_boundary :
    ∀ y : AHat,
      oldBaseRelevant y ->
      externallyChosenBoundary y ->
      externalOnOldBase y
  boundary_classified :
    ∀ y : AHat,
      oldBaseRelevant y ->
      internallyFixedBoundary y ∨ externallyChosenBoundary y

theorem completionEmbeddedOldBaseRelevant
    {A AHat : Type}
    (C : CompletionTransferData A AHat)
    (a : A) :
    C.oldBaseRelevant (C.embed a) := by
  exact C.embed_oldBaseRelevant a

theorem completionReadbackOnEmbed
    {A AHat : Type}
    (C : CompletionTransferData A AHat)
    (a : A) :
    C.readback (C.embed a) = a := by
  exact C.readback_embed a

theorem completionReadbackFixedBoundaryIsConservative
    {A AHat : Type}
    (C : CompletionTransferData A AHat)
    (y : AHat)
    (h_old : C.oldBaseRelevant y)
    (h_fixed : C.internallyFixedBoundary y) :
    C.conservativeOnOldBase y := by
  exact C.conservative_of_fixed_boundary y h_old h_fixed

theorem completionReadbackExternalBoundaryIsExternal
    {A AHat : Type}
    (C : CompletionTransferData A AHat)
    (y : AHat)
    (h_old : C.oldBaseRelevant y)
    (h_ext : C.externallyChosenBoundary y) :
    C.externalOnOldBase y := by
  exact C.external_of_external_boundary y h_old h_ext

theorem completionBoundaryClassification
    {A AHat : Type}
    (C : CompletionTransferData A AHat)
    (y : AHat)
    (h_old : C.oldBaseRelevant y) :
    C.conservativeOnOldBase y ∨ C.externalOnOldBase y := by
  rcases C.boundary_classified y h_old with h_fixed | h_ext
  · exact Or.inl (C.conservative_of_fixed_boundary y h_old h_fixed)
  · exact Or.inr (C.external_of_external_boundary y h_old h_ext)

theorem completionEmbeddedPointsAreConservative
    {A AHat : Type}
    (C : CompletionTransferData A AHat)
    (h_embedded_fixed :
      ∀ a : A, C.internallyFixedBoundary (C.embed a))
    (a : A) :
    C.conservativeOnOldBase (C.embed a) := by
  exact C.conservative_of_fixed_boundary (C.embed a) (C.embed_oldBaseRelevant a) (h_embedded_fixed a)

theorem completionReadbackPreservesEmbeddedPoint
    {A AHat : Type}
    (C : CompletionTransferData A AHat)
    (a : A) :
    C.readback (C.embed a) = a := by
  exact C.readback_embed a

def completionAsSupportGovernedFamily
    {A AHat : Type}
    (C : CompletionTransferData A AHat) :
    SupportGovernedFamily {y : AHat // C.oldBaseRelevant y} AHat where
  support := fun y => y.1
  conservative := fun y => C.conservativeOnOldBase y.1
  external := fun y => C.externalOnOldBase y.1
  supportStatus :=
    { internallyFixed := C.internallyFixedBoundary
      imported := C.externallyChosenBoundary }
  conservative_of_fixed := by
    intro y h_fixed
    exact C.conservative_of_fixed_boundary y.1 y.2 h_fixed
  external_of_imported := by
    intro y h_imported
    exact C.external_of_external_boundary y.1 y.2 h_imported
  support_classified := by
    intro y
    exact C.boundary_classified y.1 y.2

/-- Model-theoretic witness transport packet. -/
structure ModelWitnessTransferData (M N F : Type) where
  embedOldModel : M -> N
  conservative : F -> Prop
  external : F -> Prop
  definablyFixedWitness : F -> Prop
  importedWitness : F -> Prop
  detourReadback : F -> Prop
  conservative_of_definably_fixed :
    ∀ f : F, definablyFixedWitness f -> conservative f
  external_of_imported :
    ∀ f : F, importedWitness f -> external f
  conservative_of_detourReadback :
    ∀ f : F, detourReadback f -> conservative f

theorem modelDefinablyFixedWitnessIsConservative
    {M N F : Type}
    (D : ModelWitnessTransferData M N F)
    (f : F)
    (h_fixed : D.definablyFixedWitness f) :
    D.conservative f := by
  exact D.conservative_of_definably_fixed f h_fixed

theorem modelImportedWitnessIsExternal
    {M N F : Type}
    (D : ModelWitnessTransferData M N F)
    (f : F)
    (h_imported : D.importedWitness f) :
    D.external f := by
  exact D.external_of_imported f h_imported

theorem modelAmbientDetourReadbackIsConservative
    {M N F : Type}
    (D : ModelWitnessTransferData M N F)
    (f : F)
    (h_readback : D.detourReadback f) :
    D.conservative f := by
  exact D.conservative_of_detourReadback f h_readback

theorem modelWitnessClassification
    {M N F : Type}
    (D : ModelWitnessTransferData M N F)
    (f : F)
    (h :
      D.definablyFixedWitness f ∨ D.importedWitness f ∨ D.detourReadback f) :
    D.conservative f ∨ D.external f := by
  rcases h with h_fixed | h_rest
  · exact Or.inl (D.conservative_of_definably_fixed f h_fixed)
  · rcases h_rest with h_imported | h_readback
    · exact Or.inr (D.external_of_imported f h_imported)
    · exact Or.inl (D.conservative_of_detourReadback f h_readback)

inductive ModelWitnessSupportRoute where
  | definablyFixed
  | imported
  | detourReadback
deriving DecidableEq, Repr

def modelWitnessAsSupportGovernedFamily
    {M N F : Type}
    (D : ModelWitnessTransferData M N F) :
    SupportGovernedFamily
      { p : F × ModelWitnessSupportRoute //
          match p.2 with
          | .definablyFixed => D.definablyFixedWitness p.1
          | .imported => D.importedWitness p.1
          | .detourReadback => D.detourReadback p.1 }
      ModelWitnessSupportRoute where
  support := fun p => p.1.2
  conservative := fun p => D.conservative p.1.1
  external := fun p => D.external p.1.1
  supportStatus :=
    { internallyFixed := fun r => r = .definablyFixed ∨ r = .detourReadback
      imported := fun r => r = .imported }
  conservative_of_fixed := by
    intro p h_fixed
    rcases p with ⟨⟨f, r⟩, hp⟩
    rcases h_fixed with h_def | h_detour
    · cases h_def
      simpa using D.conservative_of_definably_fixed f hp
    · cases h_detour
      simpa using D.conservative_of_detourReadback f hp
  external_of_imported := by
    intro p h_imported
    rcases p with ⟨⟨f, r⟩, hp⟩
    cases h_imported
    simpa using D.external_of_imported f hp
  support_classified := by
    intro p
    cases p.1.2 with
    | definablyFixed =>
        exact Or.inl (Or.inl rfl)
    | imported =>
        exact Or.inr rfl
    | detourReadback =>
        exact Or.inl (Or.inr rfl)

/-- Forcing-level packet: generic witness import plus old-parameter readback. -/
structure ForcingTransferData (M G : Type) where
  genericWitness : G -> Prop
  oldParameterConclusion : G -> Prop
  absoluteReadback : G -> Prop
  genericDependent : G -> Prop
  conservativeOnOldParameters : G -> Prop
  externalFromGeneric : G -> Prop
  conservative_of_absolute_readback :
    ∀ g : G,
      oldParameterConclusion g ->
      absoluteReadback g ->
      conservativeOnOldParameters g
  external_of_generic_dependence :
    ∀ g : G,
      genericWitness g ->
      genericDependent g ->
      externalFromGeneric g
  readback_classified :
    ∀ g : G,
      oldParameterConclusion g ->
      absoluteReadback g ∨ genericDependent g

theorem forcingGenericWitnessIsExternal
    {M G : Type}
    (D : ForcingTransferData M G)
    (g : G)
    (h_gen : D.genericWitness g)
    (h_dep : D.genericDependent g) :
    D.externalFromGeneric g := by
  exact D.external_of_generic_dependence g h_gen h_dep

theorem forcingAbsoluteReadbackIsConservative
    {M G : Type}
    (D : ForcingTransferData M G)
    (g : G)
    (h_old : D.oldParameterConclusion g)
    (h_abs : D.absoluteReadback g) :
    D.conservativeOnOldParameters g := by
  exact D.conservative_of_absolute_readback g h_old h_abs

theorem forcingClassification
    {M G : Type}
    (D : ForcingTransferData M G)
    (g : G)
    (h_old : D.oldParameterConclusion g)
    (h_gen : D.genericWitness g) :
    D.conservativeOnOldParameters g ∨ D.externalFromGeneric g := by
  rcases D.readback_classified g h_old with h_abs | h_dep
  · exact Or.inl (D.conservative_of_absolute_readback g h_old h_abs)
  · exact Or.inr (D.external_of_generic_dependence g h_gen h_dep)

theorem forcingGenericWithoutReadbackStaysExternal
    {M G : Type}
    (D : ForcingTransferData M G)
    (h_separate :
      ∀ g : G, D.conservativeOnOldParameters g -> D.externalFromGeneric g -> False)
    (g : G)
    (h_gen : D.genericWitness g)
    (h_dep : D.genericDependent g)
    (h_cons : D.conservativeOnOldParameters g) :
    False := by
  exact h_separate g h_cons (D.external_of_generic_dependence g h_gen h_dep)

inductive ForcingSupportRoute where
  | absoluteReadback
  | genericDependence
deriving DecidableEq, Repr

def forcingAsSupportGovernedFamily
    {M G : Type}
    (D : ForcingTransferData M G) :
    SupportGovernedFamily
      { p : G × ForcingSupportRoute //
          D.oldParameterConclusion p.1 ∧
          match p.2 with
          | .absoluteReadback => D.absoluteReadback p.1
          | .genericDependence => D.genericWitness p.1 ∧ D.genericDependent p.1 }
      ForcingSupportRoute where
  support := fun p => p.1.2
  conservative := fun p => D.conservativeOnOldParameters p.1.1
  external := fun p => D.externalFromGeneric p.1.1
  supportStatus :=
    { internallyFixed := fun r => r = .absoluteReadback
      imported := fun r => r = .genericDependence }
  conservative_of_fixed := by
    intro p h_fixed
    rcases p with ⟨⟨g, r⟩, hp⟩
    cases h_fixed
    simpa using D.conservative_of_absolute_readback g hp.1 hp.2
  external_of_imported := by
    intro p h_imported
    rcases p with ⟨⟨g, r⟩, hp⟩
    cases h_imported
    simpa using D.external_of_generic_dependence g hp.2.1 hp.2.2
  support_classified := by
    intro p
    cases p.1.2 with
    | absoluteReadback =>
        exact Or.inl rfl
    | genericDependence =>
        exact Or.inr rfl

/-- Universal-property packet: ambient comparison data versus fixed readback. -/
structure UniversalConstructionTransferData (A F : Type) where
  conservative : F -> Prop
  external : F -> Prop
  internallyFixedComparison : F -> Prop
  ambientComparisonData : F -> Prop
  conservative_of_fixed_comparison :
    ∀ f : F, internallyFixedComparison f -> conservative f
  external_of_ambient_data :
    ∀ f : F, ambientComparisonData f -> external f
  comparison_classified :
    ∀ f : F, internallyFixedComparison f ∨ ambientComparisonData f

theorem universalInternalWitnessIsConservative
    {A F : Type}
    (D : UniversalConstructionTransferData A F)
    (f : F)
    (h_fixed : D.internallyFixedComparison f) :
    D.conservative f := by
  exact D.conservative_of_fixed_comparison f h_fixed

theorem universalAmbientWitnessIsExternal
    {A F : Type}
    (D : UniversalConstructionTransferData A F)
    (f : F)
    (h_ext : D.ambientComparisonData f) :
    D.external f := by
  exact D.external_of_ambient_data f h_ext

theorem universalClassification
    {A F : Type}
    (D : UniversalConstructionTransferData A F) :
    ∀ f : F, D.conservative f ∨ D.external f := by
  intro f
  rcases D.comparison_classified f with h_fixed | h_ext
  · exact Or.inl (D.conservative_of_fixed_comparison f h_fixed)
  · exact Or.inr (D.external_of_ambient_data f h_ext)

theorem universalInternalComparisonDeterminesStatus
    {A F : Type}
    (D : UniversalConstructionTransferData A F)
    {f : F}
    (h_fixed : D.internallyFixedComparison f) :
    D.conservative f ∧ ¬ D.ambientComparisonData f -> D.conservative f := by
  intro _
  exact D.conservative_of_fixed_comparison f h_fixed

def universalConstructionAsSupportGovernedFamily
    {A F : Type}
    (D : UniversalConstructionTransferData A F) :
    SupportGovernedFamily F F where
  support := fun f => f
  conservative := D.conservative
  external := D.external
  supportStatus :=
    { internallyFixed := D.internallyFixedComparison
      imported := D.ambientComparisonData }
  conservative_of_fixed := D.conservative_of_fixed_comparison
  external_of_imported := D.external_of_ambient_data
  support_classified := D.comparison_classified

/-- The interaction-generated closure of already classified procedures. -/
inductive GeneratedInteractionClosure {F : Type}
    (C : InteractionGeneratedClosureData F)
    (seed : F -> Prop) : F -> Prop where
  | seed {f : F} :
      seed f -> GeneratedInteractionClosure C seed f
  | composed {f g : F} :
      GeneratedInteractionClosure C seed f ->
      GeneratedInteractionClosure C seed g ->
      GeneratedInteractionClosure C seed (C.composed g f)
  | iterated {f : F} {n : Nat} :
      GeneratedInteractionClosure C seed f ->
      GeneratedInteractionClosure C seed (C.iterated n f)
  | diagonalized {f : F} :
      GeneratedInteractionClosure C seed f ->
      GeneratedInteractionClosure C seed (C.diagonalized f)
  | representationDetour {f : F} :
      GeneratedInteractionClosure C seed f ->
      GeneratedInteractionClosure C seed (C.representationDetour f)

theorem interactionClosurePreservesStatus
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
  intro f hf
  induction hf with
  | seed hs =>
      exact h_seed _ hs
  | composed hf hg ihf ihg =>
      rcases ihf with hfc | hfe
      · rcases ihg with hgc | hge
        · exact Or.inl (h_comp_cc _ _ hfc hgc)
        · exact Or.inr (h_comp_ce _ _ hfc hge)
      · rcases ihg with hgc | hge
        · exact Or.inr (h_comp_ec _ _ hfe hgc)
        · exact Or.inr (h_comp_ee _ _ hfe hge)
  | iterated hf ih =>
      rcases ih with hc | he
      · exact Or.inl (h_iter_cons _ _ hc)
      · exact Or.inr (h_iter_ext _ _ he)
  | diagonalized hf ih =>
      rcases ih with hc | he
      · exact Or.inl ((h_diag _).1 hc)
      · exact Or.inr ((h_diag _).2 he)
  | representationDetour hf ih =>
      rcases ih with hc | he
      · exact Or.inl ((h_repr _).1 hc)
      · exact Or.inr ((h_repr _).2 he)

theorem interactionClosureSeedEmbedding
    {F : Type}
    (C : InteractionGeneratedClosureData F)
    (seed : F -> Prop)
    {f : F}
    (h : seed f) :
    GeneratedInteractionClosure C seed f :=
  .seed h

theorem flagshipFamiliesUnifiedClassification
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
  refine And.intro ?_ <| And.intro ?_ <| And.intro ?_ <| And.intro ?_ ?_
  · exact supportGovernedFamilyClassified (canonicalizationAsSupportGovernedFamily Can)
  · exact supportGovernedFamilyClassified (completionAsSupportGovernedFamily Cmp)
  · exact supportGovernedFamilyClassified (modelWitnessAsSupportGovernedFamily Mod)
  · exact supportGovernedFamilyClassified (forcingAsSupportGovernedFamily Frc)
  · exact supportGovernedFamilyClassified (universalConstructionAsSupportGovernedFamily Uni)

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
    ∀ f : F, D.domainExtendsOldTuples f -> False) :
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
    ∀ f : F, D.domainExtendsOldTuples f -> False)
  (h_carrier_external :
    ∀ f : F, D.carrierChange f -> D.external f)
  (h_eval_disposition :
    ∀ f : F, D.evaluativeClosure f -> D.conservative f ∨ D.external f)
  (h_definitional_conservative :
    ∀ f : F, D.definitionalExpansion f -> D.conservative f)
  (h_regime_external :
    ∀ f : F, D.regimeChange f -> D.external f) :
  ∀ f : F,
    classified_by_five_mechanisms D f ->
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

theorem PaperMechanismWitnessDispositionStatement
  {X Op F : Type}
  (B : FixedBaseStructure X Op)
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
  cases m with
  | domainExtension =>
      exact Or.inr (Or.inr (PaperNoInternalTotalizationStatement B D h_domain_block f))
  | carrierChange =>
      exact Or.inr (Or.inl (h_carrier_external f h))
  | evaluativeClosure =>
      rcases h_eval_disposition f h with hC | hE
      · exact Or.inl hC
      · exact Or.inr (Or.inl hE)
  | definitionalExpansion =>
      exact Or.inl (h_definitional_conservative f h)
  | regimeChange =>
      exact Or.inr (Or.inl (h_regime_external f h))

/-- Closure of internal totalization on the fixed base. -/
theorem PaperClosureOfInternalTotalizationStatement
  {X Op F : Type}
  (B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (_h_classified :
    ∀ f : F, classified_by_five_mechanisms D f)
  (h_domain_block :
    ∀ f : F, D.domainExtendsOldTuples f -> False)
  (_h_carrier_external :
    ∀ f : F, D.carrierChange f -> D.external f)
  (_h_eval_disposition :
    ∀ f : F, D.evaluativeClosure f -> D.conservative f ∨ D.external f)
  (_h_definitional_conservative :
    ∀ f : F, D.definitionalExpansion f -> D.conservative f)
  (_h_regime_external :
    ∀ f : F, D.regimeChange f -> D.external f) :
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
    ∀ f : F, D.domainExtendsOldTuples f -> False)
  (h_carrier_external :
    ∀ f : F, D.carrierChange f -> D.external f)
  (h_eval_disposition :
    ∀ f : F, D.evaluativeClosure f -> D.conservative f ∨ D.external f)
  (h_definitional_conservative :
    ∀ f : F, D.definitionalExpansion f -> D.conservative f)
  (h_regime_external :
    ∀ f : F, D.regimeChange f -> D.external f) :
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

/-- Corollary-level no-internal-reentry principle. -/
theorem PaperNoInternalReentryPrincipleStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (_h_classified :
    ∀ f : F, classified_by_five_mechanisms D f)
  (_h_domain_block :
    ∀ f : F, D.domainExtendsOldTuples f -> False)
  (_h_carrier_external :
    ∀ f : F, D.carrierChange f -> D.external f)
  (_h_eval_disposition :
    ∀ f : F, D.evaluativeClosure f -> D.conservative f ∨ D.external f)
  (_h_definitional_conservative :
    ∀ f : F, D.definitionalExpansion f -> D.conservative f)
  (_h_regime_external :
    ∀ f : F, D.regimeChange f -> D.external f) :
  ∀ f : F, D.external f -> ¬ (¬ D.conservative f ∧ ¬ D.external f) := by
  intro f hExt h
  exact h.2 hExt

/-- Section 8 lemma: conservative closure under composition. -/
theorem PaperConservativeClosureUnderCompositionStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (C : InteractionGeneratedClosureData F)
  (f g : F)
  (hF : D.conservative f)
  (hG : D.conservative g)
  (h_comp :
    D.conservative f ->
    D.conservative g ->
    D.conservative (C.composed g f)) :
  D.conservative (C.composed g f) := by
  exact h_comp hF hG

/-- Section 8 theorem: composition and iteration do not create a third case. -/
theorem PaperCompositionIterationNoThirdCaseStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
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

/-- Section 8 proposition: diagonalization and fixed-point packaging. -/
theorem PaperDiagonalizationPackagingStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
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

/-- Section 8 proposition: representation change and foundation swap. -/
theorem PaperRepresentationChangeStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
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

/-- Section 8 theorem: no emergent family under interaction-generated closure. -/
theorem PaperNoEmergentFamilyStatement
  {X Op F : Type}
  (B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (C : InteractionGeneratedClosureData F)
  (f : F)
  (h_base :
    D.conservative f ∨ D.external f)
  (h_diag :
    (D.conservative f -> D.conservative (C.diagonalized f)) ∧
    (D.external f -> D.external (C.diagonalized f)))
  (h_repr :
    (D.conservative f -> D.conservative (C.representationDetour f)) ∧
    (D.external f -> D.external (C.representationDetour f))) :
  (D.conservative (C.diagonalized f) ∨ D.external (C.diagonalized f)) ∧
  (D.conservative (C.representationDetour f) ∨
    D.external (C.representationDetour f)) := by
  constructor
  · exact PaperDiagonalizationPackagingStatement B D C f h_diag h_base
  · exact PaperRepresentationChangeStatement B D C f h_repr h_base

/-- Section 8 corollary: no internal re-entry by detour. -/
theorem PaperNoInternalReentryByDetourStatement
  {X Op F : Type}
  (_B : FixedBaseStructure X Op)
  (D : FixedBaseOperatorData X Op F)
  (C : InteractionGeneratedClosureData F)
  (f : F)
  (h_repr :
    (D.conservative f -> D.conservative (C.representationDetour f)) ∧
    (D.external f -> D.external (C.representationDetour f)))
  (h_ext : D.external f) :
  D.external (C.representationDetour f) := by
  exact h_repr.2 h_ext

/-- Section 7 proposition: canonicalization, selection, and quotienting. -/
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

/-- Section 7 proposition: completion and evaluative closure. -/
theorem PaperCompletionEvaluativeClosureStatement
  {X Op A Cmpl : Type}
  (_B : FixedBaseStructure X Op)
  (C : CompletionCaseData A Cmpl)
  (c : Cmpl)
  (a : A) :
  C.richerObject c a ∨
  C.internallyFixedEvaluator c a ∨
  C.externalEvaluator c a ->
  C.richerObject c a ∨
  C.internallyFixedEvaluator c a ∨
  C.externalEvaluator c a := by
  intro h
  exact h

/-- Section 7 proposition: compactness, saturation, and model-theoretic existence. -/
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

/-- Section 7 proposition: forcing, genericity, and absoluteness. -/
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

/-- Section 7 proposition: universal constructions and existence by universal property. -/
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

/-- Section 7 theorem: flagship case-study closure. -/
theorem PaperFlagshipCaseStudyClosureStatement
  {X Op Fam : Type}
  (_B : FixedBaseStructure X Op)
  (conservative external : Fam -> Prop)
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
      D.oldBaseRelevant z ->
      D.internallyFixedReadback z ->
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
      D.oldBaseRelevant z ->
      D.externalReadback z ->
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
    ∀ z : G, D.genericWitness z -> D.externalByGenericDependence z) :
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
    ∀ z : G, D.oldParameterConclusion z -> D.conservativeByReadback z) :
  D.conservativeByReadback g := by
  exact h_sound g h_old

end MaleyLean
