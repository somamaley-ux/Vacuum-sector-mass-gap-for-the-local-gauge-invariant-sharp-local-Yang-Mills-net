# Unus Solus Possibilis Est Coverage Matrix

## Manuscript assets

- `papers/unus_solus_possibilis_est/main.tex`
- `papers/unus_solus_possibilis_est/Unus_Solus_Possibilis_Est.pdf`

## Lean coverage

- Section register:
  `MaleyLean/Papers/UnusSolusPossibilisEst/Verbatim/TheoremRegister.lean`
- Manuscript theorem surface:
  `MaleyLean/Papers/UnusSolusPossibilisEst/ManuscriptTheorems.lean`
- Degeneracy appendix surface:
  `MaleyLean/Papers/UnusSolusPossibilisEst/DegeneracyCases.lean`
- Axiom minimality surface:
  `MaleyLean/Papers/UnusSolusPossibilisEst/AxiomMinimality.lean`
- Independence-model surface:
  `MaleyLean/Papers/UnusSolusPossibilisEst/IndependenceModels.lean`
- Summary surface:
  `MaleyLean/Papers/UnusSolusPossibilisEst/Surface/Summary.lean`

## First-pass mapped results

- "Gate existence is forced by irreversibility + intelligibility"
- "Binary standing (when defined)"
- "No admissibility-relevant parameterization (including discrete indexing)"
- "Uniqueness of admissibility classification (no competing gates)"
- "No repairs for an evaluated act"
- "No generators"
- "Any primitive authorizer is a gate predicate"
- "No carriers (numeric or structural)"
- "No illicit scope transport"
- "Transfer without standing"
- "Reference fixation is necessary for theory-level confirmation"
- "Discrete multiplicity elimination (gate-form)"
- "Uniqueness of the admissible interior"
- "Apex Standalone Closure Theorem"
- Appendix A degeneracy cases `D1` through `D23` as separate Lean propositions/theorems
- Appendix B dependency matrix and minimal internal axiom sets
- Appendix B base model, toggle family, witness-label map, and minimal-change table
- Appendix B dropped-core witness theorems for `I`, `R`, `C`, `S`, `M`, `A`, and `B`
- Appendix B preserved-core theorems for the non-dropped cores of each toggle
- Appendix B bundled per-toggle non-dropped-core summary theorems

## Next formalization passes

- add a fuller subsection/appendix register
- connect this scaffold to upstream corpus-instantiation modules where available
