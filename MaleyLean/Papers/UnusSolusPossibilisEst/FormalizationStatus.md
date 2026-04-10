# Unus Solus Possibilis Est Formalization Status

This paper now has a completed no-axiom formalization track in `MaleyLean`.

Current status:

- manuscript source is stored at `papers/unus_solus_possibilis_est/main.tex`
- the supplied PDF is stored at `papers/unus_solus_possibilis_est/Unus_Solus_Possibilis_Est.pdf`
- the manuscript section and theorem spine has been extracted into
  `MaleyLean/Papers/UnusSolusPossibilisEst/Verbatim/TheoremRegister.lean`
- the current Lean surface now includes manuscript-level theorem encodings
- the current top summary file is
  `MaleyLean/Papers/UnusSolusPossibilisEst/Surface/Summary.lean`

What is currently formalized:

- the section-level and major-result-level manuscript register
- a manuscript-facing apex-closure system interface
- named theorem encodings for the main lemma/theorem spine of the paper
- a dedicated appendix module encoding the degeneracy cases `D1` through `D23`
- an Appendix B module encoding the axiom-result dependency matrix and minimal internal axiom sets
- an Appendix B independence-model module encoding the base model, toggle family, witness labels, minimal-change table, dropped-core witnesses, preserved-core theorems, and per-toggle non-dropped-core summary bundles
- a summary theorem bundling the current certified surface

What remains open for future deepening:

- the full appendix-by-appendix proof content beyond proposition-level degeneracy case registration
- lower-layer derivations imported from the upstream corpus manuscripts

Recommended reading order:

1. `papers/unus_solus_possibilis_est/main.tex`
2. `MaleyLean/Papers/UnusSolusPossibilisEst/Verbatim/TheoremRegister.lean`
3. `MaleyLean/Papers/UnusSolusPossibilisEst/ManuscriptTheorems.lean`
4. `MaleyLean/Papers/UnusSolusPossibilisEst/DegeneracyCases.lean`
5. `MaleyLean/Papers/UnusSolusPossibilisEst/AxiomMinimality.lean`
6. `MaleyLean/Papers/UnusSolusPossibilisEst/IndependenceModels.lean`
7. `MaleyLean/Papers/UnusSolusPossibilisEst/Surface/Summary.lean`
