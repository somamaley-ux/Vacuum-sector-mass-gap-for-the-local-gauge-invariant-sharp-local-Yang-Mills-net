import MaleyLean.Papers.YangMills.Kernel.EndpointCore

namespace MaleyLean

/--
Structured endpoint-side semantic bundle keeping dossier data, reconstruction
outputs, and endpoint closure together in one typed object.
-/
structure YMEndpointSemanticBundle (R : YMEndpointCore) where
  euclidean_input : Type
  reflection_positive : Prop
  os_data_complete : Prop
  reconstructed_hilbert : Type
  reconstruction_source_dossier : YMEndpointDossier
  reconstruction_ready : R.reconstruction_ready
  wightman_fields_present : R.reconstruction_package.wightman_fields_present
  vacuum_vector_present : R.reconstruction_package.vacuum_vector_present
  exact_endpoint : R.endpoint_object.exact_local_net_endpoint

theorem YangMillsEndpointDossierStatement
  (R : YMEndpointCore) :
  R.dossier.euclidean_input = R.dossier.euclidean_input /\
  R.dossier.reflection_positive = R.dossier.reflection_positive /\
  R.dossier.os_data_complete = R.dossier.os_data_complete := by
  exact And.intro rfl <| And.intro rfl rfl

theorem YangMillsEndpointReconstructionMetadataStatement
  (R : YMEndpointCore) :
  R.reconstruction_package.reconstructed_hilbert =
      R.reconstruction_package.reconstructed_hilbert /\
  R.reconstruction_package.from_dossier =
      R.reconstruction_package.from_dossier := by
  exact And.intro rfl rfl

def YangMillsEndpointSemanticBundleData
  (R : YMEndpointCore)
  (hE : R.euclidean_dossier_ready)
  (hP : R.endpoint_packet_ready) :
  YMEndpointSemanticBundle R := by
  have hmeta := YangMillsEndpointReconstructionMetadataStatement R
  have hnamed := YangMillsEndpointCoreExhibitsNamedOutputsStatement R hE hP
  refine
    { euclidean_input := R.dossier.euclidean_input
      reflection_positive := R.dossier.reflection_positive
      os_data_complete := R.dossier.os_data_complete
      reconstructed_hilbert := R.reconstruction_package.reconstructed_hilbert
      reconstruction_source_dossier := R.reconstruction_package.from_dossier
      reconstruction_ready := hnamed.1
      wightman_fields_present := hnamed.2.1
      vacuum_vector_present := hnamed.2.2.1
      exact_endpoint := hnamed.2.2.2 }

theorem YangMillsEndpointSemanticBundleExistsStatement
  (R : YMEndpointCore)
  (hE : R.euclidean_dossier_ready)
  (hP : R.endpoint_packet_ready) :
  Nonempty (YMEndpointSemanticBundle R) := by
  exact ⟨YangMillsEndpointSemanticBundleData R hE hP⟩

theorem YangMillsSpineFeedsEndpointSemanticBundleStatement
  (S : YMLoadBearingSpine)
  (R : YMEndpointCore)
  (h9E : S.packet9_reconstruction.euclidean_os_dossier)
  (h9W : S.packet9_reconstruction.wightman_reconstruction)
  (h10 : S.packet10_endpoint)
  (hE : R.euclidean_dossier_ready)
  (hR : R.reconstruction_ready)
  (hP : R.endpoint_packet_ready)
  (hbuild : ym_reconstruction_endpoint_core R) :
  S.packet9_reconstruction.euclidean_os_dossier /\
  S.packet9_reconstruction.wightman_reconstruction /\
  S.packet10_endpoint /\
  Nonempty (YMEndpointSemanticBundle R) := by
  have hspine :=
    YangMillsLoadBearingSpineFeedsEndpointCoreStatement
      S R h9E h9W h10 hE hR hP hbuild
  have hbundle := YangMillsEndpointSemanticBundleExistsStatement R hE hP
  exact And.intro hspine.1 <| And.intro hspine.2.1 <| And.intro hspine.2.2.1 hbundle

end MaleyLean
