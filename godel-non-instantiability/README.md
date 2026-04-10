# Godel Non-Instantiability

Standalone Lean packaging of the Godel paper surface:

`Non-Instantiability of Same-Domain Godel Threat Architectures in the Unique Admissible Interior`

This repo contains:

- the Lean import closure needed for the Godel paper module
- the current strengthened derived layer in `MaleyLean/GodelPaperStatements.lean`
- the verbatim manuscript register in `MaleyLean/GodelVerbatimRegister.lean`
- axiom audits in `Checks/Axiom/GodelAxiomCheck.lean` and `Checks/Axiom/GodelVerbatimRegisterAxiomCheck.lean`
- the paper source bundle under `paper/`

## Build

```powershell
lake build
```

## Axiom Audits

```powershell
lake env lean Checks\Axiom\GodelAxiomCheck.lean
lake env lean Checks\Axiom\GodelVerbatimRegisterAxiomCheck.lean
```

## Notes

- This standalone package was extracted from the larger `MaleyLean` workspace.
- The current Godel derived route is axiom-free.
- The `paper/` folder includes the TeX source tree present in the workspace. No compiled PDF was available in the source workspace at packaging time.
