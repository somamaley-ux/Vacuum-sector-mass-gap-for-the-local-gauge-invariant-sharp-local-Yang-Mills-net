import MaleyLean.Papers.YangMills.Surface.DependencySkeleton
import MaleyLean.Papers.YangMills.Verbatim.TheoremRegister
import MaleyLean.Papers.YangMills.Verbatim.DependencySpineSimple
import MaleyLean.Papers.YangMills.Kernel.Register
import MaleyLean.Papers.YangMills.Kernel.PacketRegister
import MaleyLean.Papers.YangMills.Kernel.ReadingOrder
import MaleyLean.Papers.YangMills.Kernel.SeamRegister
import MaleyLean.Papers.YangMills.SourceCrosswalk.Register

namespace MaleyLean

/--
Top-level manuscript-facing summary surface for the hardened Yang--Mills suite.

This theorem certifies the structural package layout extracted from the source
archive: the four live proof roots, the extracted proof kernel, the closure
gate, the reserve packet, and the first companion routing of the core paper.
-/
theorem YangMillsPaperSurfaceSummaryStatement :
  (ym_root_role .core = .liveProofSurface /\
    ym_root_role .companion1 = .liveProofSurface /\
    ym_root_role .companion2 = .liveProofSurface /\
    ym_root_role .companion3 = .liveProofSurface) /\
  (ym_root_role .proofKernel = .expertAuditKernel /\
    ym_kernel_adds_new_mathematics = False) /\
  (ym_root_role .phase9ClosureGate = .organizationalClosure) /\
  (ym_root_role .refereeDossier = .reserveMaterial /\
    ym_root_role .analyticCertificationDossier = .reserveMaterial /\
    ym_root_role .refereeConcordanceNote = .reserveMaterial /\
    ym_root_role .canonicalSourceTree = .reserveMaterial) /\
  (ym_kernel_entry_is_kernel_only_packaging .kernelMainTheorem /\
    ym_kernel_entry_is_kernel_only_packaging .tenPacketProofKernel /\
    ym_kernel_entry_to_verbatim_theorem? .continuumVacuumGapTransport =
      some .continuumVacuumGapTransport) /\
  (ym_packet_lane .packet1UVGate = .route1 /\
    ym_packet_lane .packet4FlowedState = .laneA /\
    ym_packet_lane .packet9Reconstruction = .endpoint /\
    ym_packet_lane .auxiliaryWeakWindowCertificate = .auxiliary) /\
  (ym_seam_is_kernel_only_bridge .finiteCapPositiveUnitalBridge /\
    ym_seam_is_kernel_only_bridge .boundedStateRestrictionCompatibilityNode /\
    ym_seam_to_kernel_entry? .continuumGapTransportNode =
      some .continuumVacuumGapTransport) /\
  (ym_source_labels .compactSimpleA1UltravioletGate = ["N.20"] /\
    ym_source_labels .continuumVacuumGapTransport = ["F.216"] /\
    ym_source_labels .wightmanHaagKastlerReconstruction = ["M.3"] /\
    ym_source_labels .exactLocalNetEndpointAndExclusionOfExtendedSupportSectorData = ["O.5"]) /\
  (ym_reading_track_packets .shortMassGapCompression =
      [ .packet1UVGate
      , .packet2Entrance
      , .packet3FixedLatticeGap
      , .packet8QE3Transport
      , .packet9Reconstruction
      , .packet10Endpoint
      ] /\
    ym_attack_point_seams .qe3TransportSeam =
      [ .graphCoreHandoffNode
      , .continuumGapTransportNode
      ]) /\
  (ym_verbatim_theorem_owner .compactSimpleA1UltravioletGate =
      .ultravioletGateAndRoute1 /\
    ym_verbatim_theorem_owner .finiteCapSharpLocalExtension =
      .laneASharpLocalConstruction /\
    ym_verbatim_theorem_owner .exactLocalNetEndpointAndExclusionOfExtendedSupportSectorData =
      .reconstructionAndUniversality) /\
  (ym_route1_transport_spine =
      [ .publicGroupScopeExport
      , .oneShotEntranceAtBoundedPhysicalScale
      , .tunedFullFixedLatticeOSGap
      , .sameScaleWilsonToPatchedTransport
      , .boundedWilsonDyadicOSLimitTheorem
      , .continuumTimeOSUpgradeOfBoundedBaseState
      , .continuumVacuumGapTransport
      , .continuumSharpLocalVacuumGap
      ]) /\
  (ym_core_section_owner .mainTheoremScope = none /\
    ym_core_section_owner .publicProofSpine = none /\
    ym_core_section_owner .uvGate = some .ultravioletGateAndRoute1 /\
    ym_core_section_owner .route1LatticeGap = some .ultravioletGateAndRoute1 /\
    ym_core_section_owner .laneASharpLocalConstruction =
      some .laneASharpLocalConstruction /\
    ym_core_section_owner .qe3Transport = some .ultravioletGateAndRoute1 /\
    ym_core_section_owner .endpointPacket = some .reconstructionAndUniversality /\
    ym_core_section_owner .assembly = none) := by
  refine And.intro YangMillsLiveProofSurfaceRootsStatement <|
    And.intro YangMillsKernelRoleStatement <|
    And.intro YangMillsClosureGateRoleStatement <|
    And.intro YangMillsReserveRootsStatement <|
    And.intro
      (And.intro (Or.inl rfl) <| And.intro (Or.inr rfl) rfl) <|
    And.intro YangMillsTenPacketKernelStatement <|
    And.intro
      (And.intro (Or.inl rfl) <| And.intro (Or.inr rfl) rfl) <|
    And.intro
      (And.intro rfl <| And.intro rfl <| And.intro rfl rfl) <|
    And.intro
      (And.intro rfl rfl) <|
    And.intro
      (And.intro rfl <| And.intro rfl rfl) <|
    And.intro YangMillsRoute1TransportSpineStatement
      YangMillsCoreSectionOwnershipStatement

end MaleyLean
