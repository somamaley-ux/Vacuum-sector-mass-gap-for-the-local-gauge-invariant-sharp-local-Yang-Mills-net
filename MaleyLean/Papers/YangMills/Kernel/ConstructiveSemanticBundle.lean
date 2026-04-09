import MaleyLean.Papers.YangMills.Kernel.ConstructiveCore

namespace MaleyLean

/--
Structured constructive-side semantic bundle keeping finite-cap data,
sharp-local data, and bounded-base extension together in one typed object.
-/
structure YMConstructiveSemanticBundle (R : YMConstructiveRoute) where
  truncation_window_ready : R.finite_cap_package.truncation_window_ready
  finite_cap_extension_ready : R.finite_cap_package.finite_cap_extension_ready
  positive_bridge_ready : R.finite_cap_package.positive_bridge_ready
  bounded_state_compatibility_ready : R.sharp_local_package.bounded_state_compatibility_ready
  inductive_union_ready : R.sharp_local_package.inductive_union_ready
  bounded_base_extension : R.sharp_local_package.sharp_local_state.extends_bounded_base

theorem YangMillsConstructiveSemanticBundleData
  (R : YMConstructiveRoute)
  (htrunc : R.finite_truncation_ready)
  (hext : R.finite_cap_extension_ready)
  (hcompat : R.bounded_state_compatibility_ready)
  (hunion : R.inductive_union_ready) :
  YMConstructiveSemanticBundle R := by
  have h := YangMillsConstructiveCoreExhibitsNamedOutputsStatement R htrunc hext hcompat hunion
  refine
    { truncation_window_ready := h.1
      finite_cap_extension_ready := h.2.1
      positive_bridge_ready := h.2.2.1
      bounded_state_compatibility_ready := h.2.2.2.1
      inductive_union_ready := h.2.2.2.2.1
      bounded_base_extension := h.2.2.2.2.2 }

theorem YangMillsConstructiveSemanticBundleExistsStatement
  (R : YMConstructiveRoute)
  (htrunc : R.finite_truncation_ready)
  (hext : R.finite_cap_extension_ready)
  (hcompat : R.bounded_state_compatibility_ready)
  (hunion : R.inductive_union_ready) :
  Nonempty (YMConstructiveSemanticBundle R) := by
  exact ⟨YangMillsConstructiveSemanticBundleData R htrunc hext hcompat hunion⟩

theorem YangMillsSpineFeedsConstructiveSemanticBundleStatement
  (S : YMLoadBearingSpine)
  (R : YMConstructiveRoute)
  (h4 : S.packet4_flowed_state)
  (h5 : S.packet5_finite_truncation)
  (h6 : S.packet6_finite_cap_closure.finite_cap_sharp_local_extension)
  (h7 : S.packet7_cyclicity)
  (hb : S.packet6_finite_cap_closure.positive_unital_bridge)
  (hc : S.packet6_finite_cap_closure.bounded_state_compatibility)
  (hu : S.packet6_finite_cap_closure.inductive_union_passage)
  (hflowed : R.flowed_state_ready)
  (htrunc : R.finite_truncation_ready)
  (hext : R.finite_cap_extension_ready)
  (hcyc : R.cyclicity_ready)
  (hbridge : R.finite_cap_bridge_ready)
  (hcompat : R.bounded_state_compatibility_ready)
  (hunion : R.inductive_union_ready)
  (hbuild : ym_laneA_constructive_core R) :
  S.packet4_flowed_state /\
  S.packet5_finite_truncation /\
  S.packet6_finite_cap_closure.finite_cap_sharp_local_extension /\
  S.packet7_cyclicity /\
  Nonempty (YMConstructiveSemanticBundle R) := by
  have hspine :=
    YangMillsLoadBearingSpineFeedsConstructiveCoreStatement
      S R h4 h5 h6 h7 hb hc hu
      hflowed htrunc hext hcyc hbridge hcompat hunion hbuild
  have hbundle := YangMillsConstructiveSemanticBundleExistsStatement R htrunc hext hcompat hunion
  exact And.intro hspine.1 <| And.intro hspine.2.1 <| And.intro hspine.2.2.1 <| And.intro hspine.2.2.2.1 hbundle

end MaleyLean
