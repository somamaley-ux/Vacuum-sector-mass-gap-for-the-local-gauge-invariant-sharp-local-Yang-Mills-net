import MaleyLean.PaperStatements
import MaleyLean.StandingClassifierBridge

namespace MaleyLean

/--
A candidate "lower generator" for a gate-relevant predicate on `α`.
`Lower` is the purported lower layer.
`build` maps lower-layer data to acts.
`certify` is the claimed gate-conferring rule.
-/
structure CandidateGenerator (α Lower : Type) where
  build   : Lower → α
  certify : α → Prop

/--
A first-pass failure classifier.
-/
inductive GeneratorFailure where
  | circular
  | trivial
  | illicitImport
  | extensionalCollapse
deriving Repr, DecidableEq

/--
Triviality: the generator certifies everything or certifies nothing.
-/
def trivialGenerator
  {α Lower : Type}
  (gen : CandidateGenerator α Lower) : Prop :=
  (∀ x, gen.certify x) ∨ (∀ x, ¬ gen.certify x)

/--
Extensional collapse to an existing gate `Gate`:
the purported generator does no new work.
-/
def collapsesToGate
  {α Lower : Type}
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower) : Prop :=
  ∀ x, gen.certify x ↔ Gate x

/--
A minimal first-pass notion of circularity:
the generator simply reuses the target gate as its own certification rule.
-/
def circularGenerator
  {α Lower : Type}
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower) : Prop :=
  gen.certify = Gate

/--
If a generator's certification agrees with an admissibility predicate,
it performs no independent gate work.
-/
theorem collapse_of_agreement
  {α Lower : Type}
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower)
  (h : ∀ x, gen.certify x ↔ Gate x) :
  collapsesToGate Gate gen :=
by
  exact h

/--
A relation-aware illicit-import signal:
the candidate generator assigns different gate-relevant verdicts to acts that
are equivalent under the governing redescription relation.
-/
def illicitImportWith
  {α Lower : Type}
  (rel : α → α → Prop)
  (gen : CandidateGenerator α Lower) : Prop :=
  ∃ x y : α,
    rel x y ∧
    ((gen.certify x ∧ ¬ gen.certify y) ∨
     (gen.certify y ∧ ¬ gen.certify x))

/--
A candidate generator respects redescription when lawful-redescription-equivalent
acts receive the same certification verdict.
-/
def respectsRedescription
  {α Lower : Type}
  (rel : α → α → Prop)
  (gen : CandidateGenerator α Lower) : Prop :=
  ∀ x y, rel x y → (gen.certify x ↔ gen.certify y)

/--
If a generator fails redescription invariance, then it is illicit in the
relation-aware sense.
-/
theorem illicitImportWith_of_not_respectsRedescription
  {α Lower : Type}
  (rel : α → α → Prop)
  (gen : CandidateGenerator α Lower)
  (hNR : ¬ respectsRedescription rel gen) :
  illicitImportWith rel gen :=
by
  classical
  unfold respectsRedescription at hNR
  have hx : ∃ x, ¬ ∀ y, rel x y → (gen.certify x ↔ gen.certify y) :=
    Classical.not_forall.mp hNR
  rcases hx with ⟨x, hx⟩
  have hy : ∃ y, ¬ (rel x y → (gen.certify x ↔ gen.certify y)) :=
    Classical.not_forall.mp hx
  rcases hy with ⟨y, hy⟩
  have hrel : rel x y := by
    by_cases hxy : rel x y
    · exact hxy
    · exfalso
      apply hy
      intro h
      exact False.elim (hxy h)
  have hnotiff : ¬ (gen.certify x ↔ gen.certify y) := by
    intro hiff
    apply hy
    intro _
    exact hiff
  by_cases hxC : gen.certify x
  · by_cases hyC : gen.certify y
    · exfalso
      apply hnotiff
      constructor
      · intro _
        exact hyC
      · intro _
        exact hxC
    · exact ⟨x, y, hrel, Or.inl ⟨hxC, hyC⟩⟩
  · by_cases hyC : gen.certify y
    · exact ⟨x, y, hrel, Or.inr ⟨hyC, hxC⟩⟩
    · exfalso
      apply hnotiff
      constructor
      · intro hx'
        exact False.elim (hxC hx')
      · intro hy'
        exact False.elim (hyC hy')

/--
Base classifier without relation-awareness.

Priority order:
1. circular
2. trivial
3. extensional collapse
-/
noncomputable def classify_generator
  {α Lower : Type}
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower) :
  GeneratorFailure :=
by
  classical
  by_cases hC : circularGenerator Gate gen
  · exact GeneratorFailure.circular
  · by_cases hT : trivialGenerator gen
    · exact GeneratorFailure.trivial
    · by_cases hE : collapsesToGate Gate gen
      · exact GeneratorFailure.extensionalCollapse
      · exact GeneratorFailure.extensionalCollapse

/--
Relation-aware classifier.

Priority order:
1. circular
2. trivial
3. illicit import
4. extensional collapse
-/
noncomputable def classify_generator_with_rel
  {α Lower : Type}
  (rel : α → α → Prop)
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower) :
  GeneratorFailure :=
by
  classical
  by_cases hC : circularGenerator Gate gen
  · exact GeneratorFailure.circular
  · by_cases hT : trivialGenerator gen
    · exact GeneratorFailure.trivial
    · by_cases hI : illicitImportWith rel gen
      · exact GeneratorFailure.illicitImport
      · by_cases hE : collapsesToGate Gate gen
        · exact GeneratorFailure.extensionalCollapse
        · exact GeneratorFailure.extensionalCollapse

theorem classify_generator_of_circular
  {α Lower : Type}
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower)
  (hC : circularGenerator Gate gen) :
  classify_generator Gate gen = GeneratorFailure.circular :=
by
  classical
  unfold classify_generator
  simp [hC]

theorem classify_generator_of_trivial
  {α Lower : Type}
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower)
  (hC : ¬ circularGenerator Gate gen)
  (hT : trivialGenerator gen) :
  classify_generator Gate gen = GeneratorFailure.trivial :=
by
  classical
  unfold classify_generator
  simp [hC, hT]

theorem classify_generator_of_collapse
  {α Lower : Type}
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower)
  (hC : ¬ circularGenerator Gate gen)
  (hT : ¬ trivialGenerator gen)
  (hE : collapsesToGate Gate gen) :
  classify_generator Gate gen = GeneratorFailure.extensionalCollapse :=
by
  classical
  unfold classify_generator
  simp [hC, hT, hE]

/--
If a relation-aware illicit import witness exists, the classifier returns
`illicitImport` provided the generator is not already circular or trivial.
-/
theorem classify_generator_with_rel_of_illicit
  {α Lower : Type}
  (rel : α → α → Prop)
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower)
  (hC : ¬ circularGenerator Gate gen)
  (hT : ¬ trivialGenerator gen)
  (hI : illicitImportWith rel gen) :
  classify_generator_with_rel rel Gate gen = GeneratorFailure.illicitImport :=
by
  classical
  unfold classify_generator_with_rel
  simp [hC, hT, hI]

/--
If the generator violates redescription invariance, the relation-aware
classifier forces the illicit-import branch.
-/
theorem classify_generator_with_rel_of_not_respectsRedescription
  {α Lower : Type}
  (rel : α → α → Prop)
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower)
  (hC : ¬ circularGenerator Gate gen)
  (hT : ¬ trivialGenerator gen)
  (hNR : ¬ respectsRedescription rel gen) :
  classify_generator_with_rel rel Gate gen = GeneratorFailure.illicitImport :=
by
  classical
  have hI : illicitImportWith rel gen :=
    illicitImportWith_of_not_respectsRedescription rel gen hNR
  exact classify_generator_with_rel_of_illicit rel Gate gen hC hT hI

/--
A nondegenerate gate cannot coincide extensionally with a trivial generator.
-/
theorem nontrivial_gate_blocks_trivial_collapse
  {α Lower : Type}
  (Gate : α → Prop)
  (gen : CandidateGenerator α Lower)
  (hPos : ∃ x, Gate x)
  (hNeg : ∃ y, ¬ Gate y)
  (hT : trivialGenerator gen) :
  ¬ collapsesToGate Gate gen :=
by
  intro hCollapse
  rcases hPos with ⟨x, hx⟩
  rcases hNeg with ⟨y, hy⟩
  rcases hT with hAll | hNone
  · have hyCert : gen.certify y := hAll y
    have hyGate : Gate y := (hCollapse y).mp hyCert
    exact hy hyGate
  · have hxNotCert : ¬ gen.certify x := hNone x
    have hxCert : gen.certify x := (hCollapse x).mpr hx
    exact hxNotCert hxCert

/--
If a candidate classifier captures exactly standing, it collapses to the standing gate.
This now imports the bridge module instead of rebuilding the argument locally.
-/
theorem generator_collapses_to_standing_from_bridge
  {α Lower : Type}
  (S : System α)
  (gen : CandidateGenerator α Lower)
  (h_toStanding : ∀ a : α, gen.certify a → standing S a)
  (h_fromStanding : ∀ a : α, standing S a → gen.certify a) :
  collapsesToGate (fun x => standing S x) gen :=
by
  intro a
  exact standing_classifier_extensionality S gen.certify h_toStanding h_fromStanding a

/--
If the standing gate is nondegenerate and a candidate standing-generator is
trivial but not circular, the base classifier forces the `trivial` branch.
-/
def nondegenerateStandingGate
  {α : Type}
  (S : System α) : Prop :=
  (∃ x : α, standing S x) ∧ (∃ y : α, ¬ standing S y)

theorem classify_trivial_standing_generator
  {α Lower : Type}
  (S : System α)
  (gen : CandidateGenerator α Lower)
  (_hND : nondegenerateStandingGate S)
  (hC : ¬ circularGenerator (fun x => standing S x) gen)
  (hT : trivialGenerator gen) :
  classify_generator (fun x => standing S x) gen = GeneratorFailure.trivial :=
by
  exact classify_generator_of_trivial (fun x => standing S x) gen hC hT

/--
Standing-collapse classification from the bridge:
once the candidate classifier is shown equivalent to standing, the generator
is forced into either circularity or extensional collapse.
-/
theorem classify_standing_generator_from_bridge
  {α Lower : Type}
  (S : System α)
  (gen : CandidateGenerator α Lower)
  (h_toStanding : ∀ a : α, gen.certify a → standing S a)
  (h_fromStanding : ∀ a : α, standing S a → gen.certify a)
  (hNT : ¬ trivialGenerator gen) :
  classify_generator (fun x => standing S x) gen = GeneratorFailure.extensionalCollapse ∨
  classify_generator (fun x => standing S x) gen = GeneratorFailure.circular :=
by
  classical
  have hCollapse :
    collapsesToGate (fun x => standing S x) gen :=
    generator_collapses_to_standing_from_bridge S gen h_toStanding h_fromStanding
  by_cases hC : circularGenerator (fun x => standing S x) gen
  · right
    exact classify_generator_of_circular (fun x => standing S x) gen hC
  · left
    exact classify_generator_of_collapse (fun x => standing S x) gen hC hNT hCollapse

/--
Existing carrier-style standing collapse remains available, now routed through the
bridge-based collapse theorem.
-/
theorem classify_standing_generator_from_carrier_data
  {α Lower : Type}
  (S : System α)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (gen : CandidateGenerator α Lower)
  (h_emergence :
    ∀ a : α,
      standing S a ↔
        reuse_stably_admissible
          (fun x => standing S x)
          licensed_same_scope_continuation
          preserves_relevant_invariants
          a)
  (h_gatework :
    ∀ a : α,
      gen.certify a →
        reuse_stably_admissible
          (fun x => standing S x)
          licensed_same_scope_continuation
          preserves_relevant_invariants
          a)
  (h_ext :
    ∀ a : α,
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      gen.certify a)
  (hNT : ¬ trivialGenerator gen) :
  classify_generator (fun x => standing S x) gen = GeneratorFailure.extensionalCollapse ∨
  classify_generator (fun x => standing S x) gen = GeneratorFailure.circular :=
by
  apply classify_standing_generator_from_bridge (S := S) (gen := gen)
  · intro a hq
    have hr :
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a := h_gatework a hq
    exact (h_emergence a).mpr hr
  · intro a hs
    have hr :
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a := (h_emergence a).mp hs
    exact h_ext a hr
  · exact hNT

end MaleyLean
