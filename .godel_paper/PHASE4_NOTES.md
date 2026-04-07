# Phase IV notes

This phase rewrites the coding/readback layer so that same-domain code-predicate roles are
**finitely exhausted in-paper** before diagonalization begins.

Implemented upgrades:

1. Added **Theorem 4.2**: exhaustion of same-domain code-predicate roles.
   - inert bookkeeping
   - extensional gate renaming
   - same-side refinement
   - independent standing-bearing authorizer
   - with explicit proof that no fifth role exists

2. Added elimination results for the non-bookkeeping roles:
   - **Proposition 4.3** gate-renaming collapse
   - **Proposition 4.4** same-side refinement is impossible
   - **Proposition 4.5** independent same-domain authorizers are impossible

3. Rebuilt **Theorem 4.6** as the terminal no-independent-code-predicate result,
   now derived from the explicit role-exhaustion package rather than asserted directly.

4. Added **Lemma 4.8** on representational differences:
   any same-domain representational difference is either inert bookkeeping or inferentially
   relevant in standing / trajectory structure.

5. Strengthened **Theorem 4.9** (no non-trivial admissible encoding multiplicity)
   so that its proof now visibly depends on representational collapse together with:
   - quotient uniqueness / no proper same-domain standing-preserving extension
   - no second closure-relevant equivalence relation

6. Updated the audit trail and hostile-referee reading path so that Phase IV is visible in the
   dependency spine.
