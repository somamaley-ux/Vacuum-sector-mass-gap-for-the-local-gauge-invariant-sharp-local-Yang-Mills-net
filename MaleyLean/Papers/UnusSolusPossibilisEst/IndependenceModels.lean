import MaleyLean.Papers.UnusSolusPossibilisEst.AxiomMinimality

namespace MaleyLean
namespace Papers
namespace UnusSolusPossibilisEst

inductive SigmaAtom where
  | d1 | d2
  | a0 | a1 | a2 | a3
  | e0 | e1 | e2
  | t0 | t1
  | v0 | v1 | vh | tau
deriving DecidableEq, Repr

inductive Toggle where
  | none
  | I
  | R
  | C
  | S
  | M
  | A
  | B
deriving DecidableEq, Repr

abbrev SigmaRel := SigmaAtom → SigmaAtom → Prop
abbrev SigmaFun1 := SigmaAtom → SigmaAtom
abbrev SigmaFun2 := SigmaAtom → SigmaAtom → SigmaAtom

structure SigmaModel where
  Dom : SigmaAtom → Prop
  Act : SigmaAtom → Prop
  Tar : SigmaAtom → Prop
  Val : SigmaAtom → Prop
  Ev : SigmaAtom → Prop
  Eval : SigmaRel
  Red : SigmaRel
  Same : SigmaRel
  Sub : SigmaRel
  About : SigmaRel
  LT : SigmaRel
  score : SigmaFun1
  sv : SigmaFun2

def baseModel : SigmaModel where
  Dom x := x = .d1 ∨ x = .d2
  Act x := x = .a0 ∨ x = .a1 ∨ x = .a2 ∨ x = .a3
  Tar x := x = .t0 ∨ x = .t1
  Val x := x = .v0 ∨ x = .v1 ∨ x = .vh ∨ x = .tau
  Ev x := x = .e0 ∨ x = .e1 ∨ x = .e2
  Eval d a := (d = .d1 ∨ d = .d2) ∧ (a = .a0 ∨ a = .a1 ∨ a = .a2 ∨ a = .a3)
  Red x y :=
    (x = .e0 ∧ y = .e1) ∨
    (x = .e1 ∧ y = .e2) ∨
    (x = .e0 ∧ y = .e2) ∨
    (x = .a0 ∧ y = .a1) ∨
    (x = .a1 ∧ y = .a2) ∨
    (x = .a0 ∧ y = .a2)
  Same _ _ := False
  Sub d' d := d' = .d2 ∧ d = .d1
  About e t :=
    (e = .e0 ∧ t = .t0) ∨
    (e = .e1 ∧ t = .t0) ∨
    (e = .e2 ∧ t = .t0)
  LT v w :=
    (v = .v0 ∧ w = .tau) ∨
    (v = .tau ∧ w = .v1)
  score _ := .v0
  sv _ _ := .v0

def modelForToggle : Toggle → SigmaModel
  | .none => baseModel
  | .I =>
      { baseModel with
        About := fun e t =>
          baseModel.About e t ∨ (e = .e2 ∧ t = .t1) }
  | .R =>
      { baseModel with
        Same := fun x y => x = .a2 ∧ y = .a3
        sv := fun _ x => if x = .a3 then .v1 else .v0 }
  | .C =>
      { baseModel with
        Red := fun x y =>
          ((x = .e0 ∧ y = .e1) ∨
           (x = .e1 ∧ y = .e2) ∨
           (x = .a0 ∧ y = .a1) ∨
           (x = .a1 ∧ y = .a2) ∨
           (x = .a0 ∧ y = .a2)) }
  | .S =>
      { baseModel with
        sv := fun d x => if d = .d2 ∧ x = .a3 then .v1 else .v0 }
  | .M =>
      { baseModel with
        sv := fun _ x => if x = .a1 then .v1 else .v0 }
  | .A =>
      { baseModel with
        score := fun x => if x = .a3 then .v1 else .v0
        sv := fun _ x => if x = .a3 then .v1 else .v0 }
  | .B =>
      { baseModel with
        sv := fun _ x => if x = .a3 then .vh else .v0 }

def satisfiesT0 (M : SigmaModel) : Prop :=
  M.Dom SigmaAtom.d1 ∧ M.Dom SigmaAtom.d2 ∧ SigmaAtom.d1 ≠ SigmaAtom.d2 ∧
  M.Act SigmaAtom.a0 ∧ M.Act SigmaAtom.a1 ∧ M.Act SigmaAtom.a2 ∧ M.Act SigmaAtom.a3 ∧
  M.Ev SigmaAtom.e0 ∧ M.Ev SigmaAtom.e1 ∧ M.Ev SigmaAtom.e2 ∧
  M.Tar SigmaAtom.t0 ∧ M.Tar SigmaAtom.t1 ∧
  M.Val SigmaAtom.v0 ∧ M.Val SigmaAtom.v1 ∧ M.Val SigmaAtom.vh ∧ M.Val SigmaAtom.tau ∧
  M.Sub SigmaAtom.d2 SigmaAtom.d1 ∧
  M.Eval SigmaAtom.d1 SigmaAtom.a0 ∧ M.Eval SigmaAtom.d1 SigmaAtom.a1 ∧
  M.Eval SigmaAtom.d1 SigmaAtom.a2 ∧ M.Eval SigmaAtom.d1 SigmaAtom.a3 ∧
  M.Eval SigmaAtom.d2 SigmaAtom.a0 ∧ M.Eval SigmaAtom.d2 SigmaAtom.a1 ∧
  M.Eval SigmaAtom.d2 SigmaAtom.a2 ∧ M.Eval SigmaAtom.d2 SigmaAtom.a3 ∧
  M.Red SigmaAtom.e0 SigmaAtom.e1 ∧ M.Red SigmaAtom.e1 SigmaAtom.e2 ∧
  M.Red SigmaAtom.a0 SigmaAtom.a1 ∧ M.Red SigmaAtom.a1 SigmaAtom.a2 ∧
  M.LT SigmaAtom.v0 SigmaAtom.tau ∧ M.LT SigmaAtom.tau SigmaAtom.v1

def violatesCore : Toggle → InternalAxiomTag
  | .none => .composition
  | .I => .intelligibility
  | .R => .irreversibility
  | .C => .composition
  | .S => .scopeDiscipline
  | .M => .miax
  | .A => .ametricBoundary
  | .B => .bivalence

def witnessFormulaLabel : Toggle → String
  | .none => "Base model M0"
  | .I => reopenedDegeneracyForDroppedAxiom .intelligibility
  | .R => reopenedDegeneracyForDroppedAxiom .irreversibility
  | .C => reopenedDegeneracyForDroppedAxiom .composition
  | .S => reopenedDegeneracyForDroppedAxiom .scopeDiscipline
  | .M => reopenedDegeneracyForDroppedAxiom .miax
  | .A => reopenedDegeneracyForDroppedAxiom .ametricBoundary
  | .B => reopenedDegeneracyForDroppedAxiom .bivalence

def hammingDistanceFromBase : Toggle → Nat
  | .none => 0
  | .I => 1
  | .R => 3
  | .C => 1
  | .S => 1
  | .M => 2
  | .A => 3
  | .B => 2

def intelligibilityCore (M : SigmaModel) : Prop :=
  ∀ e e' t,
    M.Ev e → M.Ev e' → M.Red e e' → (M.About e t ↔ M.About e' t)

def irreversibilityCore (M : SigmaModel) : Prop :=
  ∀ d a a',
    M.Dom d → M.Act a → M.Act a' → M.Eval d a → M.Eval d a' → M.Same a a' →
    M.sv d a = M.sv d a'

def compositionCore (M : SigmaModel) : Prop :=
  ∀ x y z, M.Red x y → M.Red y z → M.Red x z

def scopeDisciplineCore (M : SigmaModel) : Prop :=
  ∀ d d' a,
    M.Dom d → M.Dom d' → M.Act a → M.Sub d' d → M.Eval d a → M.Eval d' a →
    M.sv d' a = M.sv d a

def miaxCore (M : SigmaModel) : Prop :=
  ∀ d a a',
    M.Dom d → M.Act a → M.Act a' → M.Eval d a → M.Eval d a' → M.Red a a' →
    M.sv d a = M.sv d a'

def ametricCore (M : SigmaModel) : Prop :=
  ∀ a b, M.Act a → M.Act b → M.score a = M.score b

def bivalenceCore (M : SigmaModel) : Prop :=
  ∀ d a, M.Dom d → M.Act a → M.Eval d a →
    (M.sv d a = SigmaAtom.v0 ∨ M.sv d a = SigmaAtom.v1)

def fixationDriftWitness (M : SigmaModel) : Prop :=
  ∃ e e',
    M.Ev e ∧ M.Ev e' ∧ M.Red e e' ∧ M.About e SigmaAtom.t0 ∧ M.About e' SigmaAtom.t1

def sameActRepairWitness (M : SigmaModel) : Prop :=
  ∃ d,
    M.Dom d ∧ M.Same SigmaAtom.a2 SigmaAtom.a3 ∧
    M.Eval d SigmaAtom.a2 ∧ M.Eval d SigmaAtom.a3 ∧
    M.sv d SigmaAtom.a2 = SigmaAtom.v0 ∧ M.sv d SigmaAtom.a3 = SigmaAtom.v1

def nonCompositionWitness (M : SigmaModel) : Prop :=
  M.Red SigmaAtom.e0 SigmaAtom.e1 ∧
  M.Red SigmaAtom.e1 SigmaAtom.e2 ∧
  ¬ M.Red SigmaAtom.e0 SigmaAtom.e2

def scopeLegalizationWitness (M : SigmaModel) : Prop :=
  M.Sub SigmaAtom.d2 SigmaAtom.d1 ∧
  M.Eval SigmaAtom.d1 SigmaAtom.a3 ∧
  M.Eval SigmaAtom.d2 SigmaAtom.a3 ∧
  M.sv SigmaAtom.d1 SigmaAtom.a3 = SigmaAtom.v0 ∧
  M.sv SigmaAtom.d2 SigmaAtom.a3 = SigmaAtom.v1

def redescriptionVariantStandingWitness (M : SigmaModel) : Prop :=
  ∃ d,
    M.Dom d ∧ M.Red SigmaAtom.a0 SigmaAtom.a1 ∧
    M.Eval d SigmaAtom.a0 ∧ M.Eval d SigmaAtom.a1 ∧
    M.sv d SigmaAtom.a0 = SigmaAtom.v0 ∧ M.sv d SigmaAtom.a1 = SigmaAtom.v1

def thresholdCarrierWitness (M : SigmaModel) : Prop :=
  ∃ d,
    M.Dom d ∧ ¬ M.LT SigmaAtom.tau (M.score SigmaAtom.a0) ∧
    M.LT SigmaAtom.tau (M.score SigmaAtom.a3) ∧
    ∀ x, M.Act x ∧ M.Eval d x →
      (M.sv d x = SigmaAtom.v1 ↔ M.LT SigmaAtom.tau (M.score x))

def thirdStandingValueWitness (M : SigmaModel) : Prop :=
  ∃ d, M.Dom d ∧ M.Eval d SigmaAtom.a3 ∧ M.sv d SigmaAtom.a3 = SigmaAtom.vh

theorem base_model_satisfies_T0 :
    satisfiesT0 baseModel := by
  simp [satisfiesT0, baseModel]

theorem every_toggle_preserves_T0 :
    ∀ θ : Toggle, satisfiesT0 (modelForToggle θ) := by
  intro θ
  cases θ <;> simp [modelForToggle, satisfiesT0, baseModel]

theorem base_toggle_is_base_model :
    modelForToggle .none = baseModel := by
  rfl

theorem uniform_independence_witness_label
    (θ : Toggle) :
    θ = .none ∨
    witnessFormulaLabel θ =
      reopenedDegeneracyForDroppedAxiom (violatesCore θ) := by
  cases θ <;> simp [witnessFormulaLabel, violatesCore]

theorem minimal_change_toggle_distance
    (θ : Toggle) :
    hammingDistanceFromBase θ =
      match θ with
      | .none => 0
      | .I => 1
      | .R => 3
      | .C => 1
      | .S => 1
      | .M => 2
      | .A => 3
      | .B => 2 := by
  cases θ <;> rfl

theorem minimal_change_table_I :
    hammingDistanceFromBase .I = 1 := by
  rfl

theorem minimal_change_table_R :
    hammingDistanceFromBase .R = 3 := by
  rfl

theorem minimal_change_table_C :
    hammingDistanceFromBase .C = 1 := by
  rfl

theorem minimal_change_table_S :
    hammingDistanceFromBase .S = 1 := by
  rfl

theorem minimal_change_table_M :
    hammingDistanceFromBase .M = 2 := by
  rfl

theorem minimal_change_table_A :
    hammingDistanceFromBase .A = 3 := by
  rfl

theorem minimal_change_table_B :
    hammingDistanceFromBase .B = 2 := by
  rfl

theorem base_model_satisfies_irreversibility_core :
    irreversibilityCore baseModel := by
  intro d a a' hD hA hA' hEval hEval' hSame
  simp [baseModel] at hSame

theorem base_model_satisfies_intelligibility_core :
    intelligibilityCore baseModel := by
  intro e e' t hE hE' hRed
  rcases hE with rfl | rfl | rfl <;>
    rcases hE' with rfl | rfl | rfl <;>
    simp [baseModel] at hRed ⊢

theorem base_model_satisfies_composition_core :
    compositionCore baseModel := by
  intro x y z hxy hyz
  rcases hxy with hxy | hxy | hxy | hxy | hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    rcases hyz with hyz | hyz | hyz | hyz | hyz | hyz
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨_, rfl⟩
      simp [baseModel]
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
  · rcases hxy with ⟨rfl, rfl⟩
    rcases hyz with hyz | hyz | hyz | hyz | hyz | hyz
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
  · rcases hxy with ⟨rfl, rfl⟩
    rcases hyz with hyz | hyz | hyz | hyz | hyz | hyz
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
  · rcases hxy with ⟨rfl, rfl⟩
    rcases hyz with hyz | hyz | hyz | hyz | hyz | hyz
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨_, rfl⟩
      simp [baseModel]
    · rcases hyz with ⟨h, _⟩
      simp at h
  · rcases hxy with ⟨rfl, rfl⟩
    rcases hyz with hyz | hyz | hyz | hyz | hyz | hyz
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
  · rcases hxy with ⟨rfl, rfl⟩
    rcases hyz with hyz | hyz | hyz | hyz | hyz | hyz
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h
    · rcases hyz with ⟨h, _⟩
      simp at h

theorem base_model_satisfies_scope_discipline_core :
    scopeDisciplineCore baseModel := by
  intro d d' a hD hD' hA hSub hEval hEval'
  simp [baseModel]

theorem base_model_satisfies_miax_core :
    miaxCore baseModel := by
  intro d a a' hD hA hA' hEval hEval' hRed
  simp [baseModel]

theorem base_model_satisfies_ametric_core :
    ametricCore baseModel := by
  intro a b hA hB
  simp [baseModel]

theorem base_model_satisfies_bivalence_core :
    bivalenceCore baseModel := by
  intro d a hD hA hEval
  simp [baseModel]

theorem toggle_I_violates_intelligibility :
    ¬ intelligibilityCore (modelForToggle .I) := by
  intro h
  have hRed : (modelForToggle .I).Red SigmaAtom.e1 SigmaAtom.e2 := by
    simp [modelForToggle, baseModel]
  have hE1 : (modelForToggle .I).Ev SigmaAtom.e1 := by
    simp [modelForToggle, baseModel]
  have hE2 : (modelForToggle .I).Ev SigmaAtom.e2 := by
    simp [modelForToggle, baseModel]
  have hiff := h SigmaAtom.e1 SigmaAtom.e2 SigmaAtom.t1 hE1 hE2 hRed
  have hLeft : ¬ (modelForToggle .I).About SigmaAtom.e1 SigmaAtom.t1 := by
    simp [modelForToggle, baseModel]
  have hRight : (modelForToggle .I).About SigmaAtom.e2 SigmaAtom.t1 := by
    simp [modelForToggle, baseModel]
  exact hLeft ((hiff).mpr hRight)

theorem toggle_I_has_fixation_drift_witness :
    fixationDriftWitness (modelForToggle .I) := by
  refine ⟨SigmaAtom.e1, SigmaAtom.e2, ?_⟩
  simp [modelForToggle, baseModel]

theorem toggle_C_violates_composition :
    ¬ compositionCore (modelForToggle .C) := by
  intro h
  have h01 : (modelForToggle .C).Red SigmaAtom.e0 SigmaAtom.e1 := by
    simp [modelForToggle, baseModel]
  have h12 : (modelForToggle .C).Red SigmaAtom.e1 SigmaAtom.e2 := by
    simp [modelForToggle, baseModel]
  have h02 := h SigmaAtom.e0 SigmaAtom.e1 SigmaAtom.e2 h01 h12
  simp [modelForToggle, baseModel] at h02

theorem toggle_C_has_noncomposition_witness :
    nonCompositionWitness (modelForToggle .C) := by
  simp [nonCompositionWitness, modelForToggle, baseModel]

theorem toggle_S_violates_scope_discipline :
    ¬ scopeDisciplineCore (modelForToggle .S) := by
  intro h
  have hEq :=
    h SigmaAtom.d1 SigmaAtom.d2 SigmaAtom.a3
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
  simp [modelForToggle, baseModel] at hEq

theorem toggle_S_has_scope_legalization_witness :
    scopeLegalizationWitness (modelForToggle .S) := by
  simp [scopeLegalizationWitness, modelForToggle, baseModel]

theorem toggle_R_violates_irreversibility :
    ¬ irreversibilityCore (modelForToggle .R) := by
  intro h
  have hEq :=
    h SigmaAtom.d1 SigmaAtom.a2 SigmaAtom.a3
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
  simp [modelForToggle, baseModel] at hEq

theorem toggle_R_has_same_act_repair_witness :
    sameActRepairWitness (modelForToggle .R) := by
  refine ⟨SigmaAtom.d1, ?_⟩
  simp [modelForToggle, baseModel]

theorem toggle_M_violates_miax :
    ¬ miaxCore (modelForToggle .M) := by
  intro h
  have hEq :=
    h SigmaAtom.d1 SigmaAtom.a0 SigmaAtom.a1
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
  simp [modelForToggle, baseModel] at hEq

theorem toggle_M_has_redescription_variant_standing_witness :
    redescriptionVariantStandingWitness (modelForToggle .M) := by
  refine ⟨SigmaAtom.d1, ?_⟩
  simp [modelForToggle, baseModel]

theorem toggle_A_violates_ametric :
    ¬ ametricCore (modelForToggle .A) := by
  intro h
  have hEq :=
    h SigmaAtom.a0 SigmaAtom.a3
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
  simp [modelForToggle, baseModel] at hEq

theorem toggle_A_has_threshold_carrier_witness :
    thresholdCarrierWitness (modelForToggle .A) := by
  refine ⟨SigmaAtom.d1, ?_⟩
  simp [modelForToggle, baseModel]

theorem toggle_B_violates_bivalence :
    ¬ bivalenceCore (modelForToggle .B) := by
  intro h
  have hCase :=
    h SigmaAtom.d1 SigmaAtom.a3
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
      (by simp [modelForToggle, baseModel])
  simp [modelForToggle, baseModel] at hCase

theorem toggle_B_has_third_value_witness :
    thirdStandingValueWitness (modelForToggle .B) := by
  refine ⟨SigmaAtom.d1, ?_⟩
  simp [modelForToggle, baseModel]

theorem toggle_I_preserves_irreversibility_core :
    irreversibilityCore (modelForToggle .I) := by
  simpa [modelForToggle] using base_model_satisfies_irreversibility_core

theorem toggle_I_preserves_scope_discipline_core :
    scopeDisciplineCore (modelForToggle .I) := by
  simpa [modelForToggle] using base_model_satisfies_scope_discipline_core

theorem toggle_I_preserves_composition_core :
    compositionCore (modelForToggle .I) := by
  simpa [modelForToggle] using base_model_satisfies_composition_core

theorem toggle_I_preserves_miax_core :
    miaxCore (modelForToggle .I) := by
  simpa [modelForToggle] using base_model_satisfies_miax_core

theorem toggle_I_preserves_ametric_core :
    ametricCore (modelForToggle .I) := by
  simpa [modelForToggle] using base_model_satisfies_ametric_core

theorem toggle_I_preserves_bivalence_core :
    bivalenceCore (modelForToggle .I) := by
  simpa [modelForToggle] using base_model_satisfies_bivalence_core

theorem toggle_C_preserves_intelligibility_core :
    intelligibilityCore (modelForToggle .C) := by
  intro e e' t hE hE' hRed
  rcases hE with rfl | rfl | rfl <;>
    rcases hE' with rfl | rfl | rfl <;>
    simp [modelForToggle, baseModel] at hRed ⊢

theorem toggle_C_preserves_irreversibility_core :
    irreversibilityCore (modelForToggle .C) := by
  simpa [modelForToggle] using base_model_satisfies_irreversibility_core

theorem toggle_C_preserves_scope_discipline_core :
    scopeDisciplineCore (modelForToggle .C) := by
  simpa [modelForToggle] using base_model_satisfies_scope_discipline_core

theorem toggle_C_preserves_ametric_core :
    ametricCore (modelForToggle .C) := by
  simpa [modelForToggle] using base_model_satisfies_ametric_core

theorem toggle_C_preserves_bivalence_core :
    bivalenceCore (modelForToggle .C) := by
  simpa [modelForToggle] using base_model_satisfies_bivalence_core

theorem toggle_C_preserves_miax_core :
    miaxCore (modelForToggle .C) := by
  intro d a a' hD hA hA' hEval hEval' hRed
  simp [modelForToggle, baseModel] at hRed ⊢

theorem toggle_R_preserves_intelligibility_core :
    intelligibilityCore (modelForToggle .R) := by
  simpa [modelForToggle] using base_model_satisfies_intelligibility_core

theorem toggle_R_preserves_scope_discipline_core :
    scopeDisciplineCore (modelForToggle .R) := by
  intro d d' a hD hD' hA hSub hEval hEval'
  simp [modelForToggle, baseModel]

theorem toggle_R_preserves_composition_core :
    compositionCore (modelForToggle .R) := by
  simpa [modelForToggle] using base_model_satisfies_composition_core

theorem toggle_R_preserves_ametric_core :
    ametricCore (modelForToggle .R) := by
  simpa [modelForToggle] using base_model_satisfies_ametric_core

theorem toggle_R_preserves_bivalence_core :
    bivalenceCore (modelForToggle .R) := by
  intro d a hD hA hEval
  by_cases h3 : a = SigmaAtom.a3 <;> simp [modelForToggle, baseModel, h3]

theorem toggle_R_preserves_miax_core :
    miaxCore (modelForToggle .R) := by
  intro d a a' hD hA hA' hEval hEval' hRed
  rcases hRed with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]

theorem toggle_S_preserves_intelligibility_core :
    intelligibilityCore (modelForToggle .S) := by
  simpa [modelForToggle] using base_model_satisfies_intelligibility_core

theorem toggle_S_preserves_irreversibility_core :
    irreversibilityCore (modelForToggle .S) := by
  intro d a a' hD hA hA' hEval hEval' hSame
  simp [modelForToggle, baseModel] at hSame

theorem toggle_S_preserves_composition_core :
    compositionCore (modelForToggle .S) := by
  simpa [modelForToggle] using base_model_satisfies_composition_core

theorem toggle_S_preserves_ametric_core :
    ametricCore (modelForToggle .S) := by
  simpa [modelForToggle] using base_model_satisfies_ametric_core

theorem toggle_S_preserves_bivalence_core :
    bivalenceCore (modelForToggle .S) := by
  intro d a hD hA hEval
  by_cases hda : d = SigmaAtom.d2 ∧ a = SigmaAtom.a3 <;> simp [modelForToggle, baseModel, hda]

theorem toggle_S_preserves_miax_core :
    miaxCore (modelForToggle .S) := by
  intro d a a' hD hA hA' hEval hEval' hRed
  rcases hRed with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]

theorem toggle_M_preserves_intelligibility_core :
    intelligibilityCore (modelForToggle .M) := by
  simpa [modelForToggle] using base_model_satisfies_intelligibility_core

theorem toggle_M_preserves_irreversibility_core :
    irreversibilityCore (modelForToggle .M) := by
  intro d a a' hD hA hA' hEval hEval' hSame
  simp [modelForToggle, baseModel] at hSame

theorem toggle_M_preserves_composition_core :
    compositionCore (modelForToggle .M) := by
  simpa [modelForToggle] using base_model_satisfies_composition_core

theorem toggle_M_preserves_scope_discipline_core :
    scopeDisciplineCore (modelForToggle .M) := by
  intro d d' a hD hD' hA hSub hEval hEval'
  simp [modelForToggle, baseModel]

theorem toggle_M_preserves_ametric_core :
    ametricCore (modelForToggle .M) := by
  simpa [modelForToggle] using base_model_satisfies_ametric_core

theorem toggle_M_preserves_bivalence_core :
    bivalenceCore (modelForToggle .M) := by
  intro d a hD hA hEval
  by_cases h1 : a = SigmaAtom.a1 <;> simp [modelForToggle, baseModel, h1]

theorem toggle_A_preserves_intelligibility_core :
    intelligibilityCore (modelForToggle .A) := by
  simpa [modelForToggle] using base_model_satisfies_intelligibility_core

theorem toggle_A_preserves_irreversibility_core :
    irreversibilityCore (modelForToggle .A) := by
  intro d a a' hD hA hA' hEval hEval' hSame
  simp [modelForToggle, baseModel] at hSame

theorem toggle_A_preserves_composition_core :
    compositionCore (modelForToggle .A) := by
  simpa [modelForToggle] using base_model_satisfies_composition_core

theorem toggle_A_preserves_scope_discipline_core :
    scopeDisciplineCore (modelForToggle .A) := by
  intro d d' a hD hD' hA hSub hEval hEval'
  simp [modelForToggle, baseModel]

theorem toggle_A_preserves_bivalence_core :
    bivalenceCore (modelForToggle .A) := by
  intro d a hD hA hEval
  by_cases h3 : a = SigmaAtom.a3 <;> simp [modelForToggle, baseModel, h3]

theorem toggle_A_preserves_miax_core :
    miaxCore (modelForToggle .A) := by
  intro d a a' hD hA hA' hEval hEval' hRed
  rcases hRed with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]

theorem toggle_B_preserves_intelligibility_core :
    intelligibilityCore (modelForToggle .B) := by
  simpa [modelForToggle] using base_model_satisfies_intelligibility_core

theorem toggle_B_preserves_irreversibility_core :
    irreversibilityCore (modelForToggle .B) := by
  intro d a a' hD hA hA' hEval hEval' hSame
  simp [modelForToggle, baseModel] at hSame

theorem toggle_B_preserves_composition_core :
    compositionCore (modelForToggle .B) := by
  simpa [modelForToggle] using base_model_satisfies_composition_core

theorem toggle_B_preserves_scope_discipline_core :
    scopeDisciplineCore (modelForToggle .B) := by
  intro d d' a hD hD' hA hSub hEval hEval'
  simp [modelForToggle, baseModel]

theorem toggle_B_preserves_ametric_core :
    ametricCore (modelForToggle .B) := by
  simpa [modelForToggle] using base_model_satisfies_ametric_core

theorem toggle_B_preserves_miax_core :
    miaxCore (modelForToggle .B) := by
  intro d a a' hD hA hA' hEval hEval' hRed
  rcases hRed with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel] at hA
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]
  · rcases h with ⟨rfl, rfl⟩
    simp [modelForToggle, baseModel]

theorem toggle_I_preserves_all_nondropped_cores :
    irreversibilityCore (modelForToggle .I) ∧
    compositionCore (modelForToggle .I) ∧
    scopeDisciplineCore (modelForToggle .I) ∧
    miaxCore (modelForToggle .I) ∧
    ametricCore (modelForToggle .I) ∧
    bivalenceCore (modelForToggle .I) := by
  exact ⟨toggle_I_preserves_irreversibility_core,
    toggle_I_preserves_composition_core,
    toggle_I_preserves_scope_discipline_core,
    toggle_I_preserves_miax_core,
    toggle_I_preserves_ametric_core,
    toggle_I_preserves_bivalence_core⟩

theorem toggle_C_preserves_all_nondropped_cores :
    intelligibilityCore (modelForToggle .C) ∧
    irreversibilityCore (modelForToggle .C) ∧
    scopeDisciplineCore (modelForToggle .C) ∧
    miaxCore (modelForToggle .C) ∧
    ametricCore (modelForToggle .C) ∧
    bivalenceCore (modelForToggle .C) := by
  exact ⟨toggle_C_preserves_intelligibility_core,
    toggle_C_preserves_irreversibility_core,
    toggle_C_preserves_scope_discipline_core,
    toggle_C_preserves_miax_core,
    toggle_C_preserves_ametric_core,
    toggle_C_preserves_bivalence_core⟩

theorem toggle_R_preserves_all_nondropped_cores :
    intelligibilityCore (modelForToggle .R) ∧
    compositionCore (modelForToggle .R) ∧
    scopeDisciplineCore (modelForToggle .R) ∧
    miaxCore (modelForToggle .R) ∧
    ametricCore (modelForToggle .R) ∧
    bivalenceCore (modelForToggle .R) := by
  exact ⟨toggle_R_preserves_intelligibility_core,
    toggle_R_preserves_composition_core,
    toggle_R_preserves_scope_discipline_core,
    toggle_R_preserves_miax_core,
    toggle_R_preserves_ametric_core,
    toggle_R_preserves_bivalence_core⟩

theorem toggle_S_preserves_all_nondropped_cores :
    intelligibilityCore (modelForToggle .S) ∧
    irreversibilityCore (modelForToggle .S) ∧
    compositionCore (modelForToggle .S) ∧
    miaxCore (modelForToggle .S) ∧
    ametricCore (modelForToggle .S) ∧
    bivalenceCore (modelForToggle .S) := by
  exact ⟨toggle_S_preserves_intelligibility_core,
    toggle_S_preserves_irreversibility_core,
    toggle_S_preserves_composition_core,
    toggle_S_preserves_miax_core,
    toggle_S_preserves_ametric_core,
    toggle_S_preserves_bivalence_core⟩

theorem toggle_M_preserves_all_nondropped_cores :
    intelligibilityCore (modelForToggle .M) ∧
    irreversibilityCore (modelForToggle .M) ∧
    compositionCore (modelForToggle .M) ∧
    scopeDisciplineCore (modelForToggle .M) ∧
    ametricCore (modelForToggle .M) ∧
    bivalenceCore (modelForToggle .M) := by
  exact ⟨toggle_M_preserves_intelligibility_core,
    toggle_M_preserves_irreversibility_core,
    toggle_M_preserves_composition_core,
    toggle_M_preserves_scope_discipline_core,
    toggle_M_preserves_ametric_core,
    toggle_M_preserves_bivalence_core⟩

theorem toggle_A_preserves_all_nondropped_cores :
    intelligibilityCore (modelForToggle .A) ∧
    irreversibilityCore (modelForToggle .A) ∧
    compositionCore (modelForToggle .A) ∧
    scopeDisciplineCore (modelForToggle .A) ∧
    miaxCore (modelForToggle .A) ∧
    bivalenceCore (modelForToggle .A) := by
  exact ⟨toggle_A_preserves_intelligibility_core,
    toggle_A_preserves_irreversibility_core,
    toggle_A_preserves_composition_core,
    toggle_A_preserves_scope_discipline_core,
    toggle_A_preserves_miax_core,
    toggle_A_preserves_bivalence_core⟩

theorem toggle_B_preserves_all_nondropped_cores :
    intelligibilityCore (modelForToggle .B) ∧
    irreversibilityCore (modelForToggle .B) ∧
    compositionCore (modelForToggle .B) ∧
    scopeDisciplineCore (modelForToggle .B) ∧
    miaxCore (modelForToggle .B) ∧
    ametricCore (modelForToggle .B) := by
  exact ⟨toggle_B_preserves_intelligibility_core,
    toggle_B_preserves_irreversibility_core,
    toggle_B_preserves_composition_core,
    toggle_B_preserves_scope_discipline_core,
    toggle_B_preserves_miax_core,
    toggle_B_preserves_ametric_core⟩

end UnusSolusPossibilisEst
end Papers
end MaleyLean
