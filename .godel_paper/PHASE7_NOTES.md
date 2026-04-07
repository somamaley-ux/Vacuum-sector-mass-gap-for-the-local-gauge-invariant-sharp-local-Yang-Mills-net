# Phase VII notes

This phase implements the **terminal-theorem reordering** from the hardening plan.

## What changed

1. **Moved the bridge-compression and ordinary-formal-system filter forward**
   - `G\"odel threat alignment` and the `Translation filter for ordinary G\"odel objections` are now placed at the end of Section 5, after the rescue-route package is fully closed.
   - This keeps Section 6 from doing intermediate proof work before the terminal theorem.

2. **Retitled Section 6 as a terminal section**
   - Section 6 is now `Terminal theorem and corollaries`.
   - Its opening paragraph explicitly states that the previous sections have already closed every same-domain route by which an incompleteness objection could acquire governance force.

3. **Inserted a new pre-main-theorem exhaustion theorem**
   - Added `Theorem 6.1`:
     - **Exhaustion of same-domain incompleteness objection routes**
   - It classifies every alleged same-domain incompleteness objection into exactly six routes:
     1. code-level readback,
     2. semantic or meta-foundational import,
     3. reflection / infinitary rule-power,
     4. second-equivalence or parallel-quotient route,
     5. richer same-domain extension or new-gate route,
     6. explicit scope change.
   - The proof then eliminates the first five as impossible or closure-inert and identifies the sixth as non-same-domain.

4. **Rewrote the main theorem proof to be terminal**
   - `Theorem 6.2` now depends directly on:
     - the alignment theorem, and
     - the new route-exhaustion theorem.
   - The proof no longer replays the entire prerequisite chain in compressed form. Instead it points back to the already exhausted route theorem and closes by contradiction.

5. **Updated the summary sentence after the main theorem**
   - The summary now explicitly states that every same-domain incompleteness objection route has already been exhausted before the main theorem is stated.

6. **Updated audit packaging**
   - Added a new audit-trail row for `Theorem 6.1`.
   - Updated the main-theorem dependency row so it now reads as a terminal contradiction of exhausted routes.
   - Updated the hostile-referee reading path so a referee can move directly from the route-exhaustion theorem to the main theorem.

## Result of Phase VII

The paper now satisfies the Phase VII target from the upgrade plan:

- Section 6 reads as a **terminal theorem section**, not as a place where new proof-bearing machinery is still being improvised.
- A referee can now skip from the route-exhaustion theorem to the main theorem and see that only the terminal contradiction remains.
