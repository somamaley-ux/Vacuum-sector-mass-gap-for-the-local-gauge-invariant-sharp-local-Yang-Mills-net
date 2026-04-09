namespace MaleyLean

/--
Standard imported OS/Wightman background used by the endpoint packet.

This is not manuscript-specific Yang--Mills mathematics. It isolates the
background reconstruction/analytic-continuation/uniqueness machinery that the
paper cites as imported standard input.
-/
structure YMStandardOSWightmanBackground
    (dossier_ready : Prop)
    (vacuum_vector_present : Prop)
    (wightman_fields_present : Prop)
    (smearing_defined : Prop)
    (vacuum_correlations_defined : Prop) where
  reconstruction_ready : Prop
  dossier_implies_reconstruction :
    dossier_ready -> reconstruction_ready
  reconstruction_exhibits_vacuum :
    reconstruction_ready -> vacuum_vector_present
  reconstruction_exhibits_fields :
    reconstruction_ready -> wightman_fields_present
  reconstruction_exhibits_smearing :
    reconstruction_ready -> smearing_defined
  reconstruction_exhibits_vacuum_correlations :
    reconstruction_ready -> vacuum_correlations_defined

end MaleyLean
