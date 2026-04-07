# Phase III notes — inferential exhaustion bridge rebuild

This phase implements the Phase III targets from `godel_paper_hardening_upgrade_plan.pdf`.

## Core upgrades made

1. **Closure threat definition broadened**
   - `Closure threat` is no longer defined directly in terms of standing or trajectory divergence.
   - The paper now defines the broader notion of the fixed domain's **inferential life** and defines closure threat as any same-domain distinction that changes that inferential life.

2. **Three-step bridge chain inserted in Section 3**
   - Added **Lemma 3.10**: *Fixed-domain inferential-life exhaustion*.
   - Added **Lemma 3.11**: *Closure-relevance transmission*.
   - Rewrote **Theorem 3.12** (*Inferential Necessity of Closure Distinctions*) so it is now the terminal consequence of those two lemmas plus the quotient / trajectory / equivalence results already proved in Appendices C–E.

3. **Trajectory-only corollary corrected**
   - Removed the old over-strong trajectory lemma and replaced it with a correct corollary:
     - **Corollary 3.14**: *Trajectory-neutral closure relevance is act-level*.

4. **Governance-relevant readback proofs updated**
   - The hidden gate-work lemma and the no-independent-code-predicate proof now treat governance relevance as change in inferential life, and then invoke the revised bridge theorem to force that change into standing or trajectory structure.

5. **Audit controls updated**
   - The audit trail now lists the new inferential-exhaustion lemmas explicitly.
   - The hostile-referee reading path now routes through the new Section 3 chain before the coding and diagonal sections.

## Why this phase matters

This phase removes the main "you defined closure relevance to mean standing relevance" objection. The paper now proves that bridge instead of building it into the closure-threat definition.
