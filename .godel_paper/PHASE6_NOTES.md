# Phase VI notes

This phase expands the rescue-route blocking layer so the paper no longer relies on a single
compressed proposition for semantic and infinitary escape routes.

Implemented upgrades:

1. Replaced the former compact rescue proposition with an explicit theorem sequence in
   Section 5.
   - **Theorem 5.6** (`thm:no-semantic-import`): no semantic standing import on the old scope.
   - **Theorem 5.8** (`thm:no-meta-reanchoring`): no same-domain meta-foundational re-anchoring.

2. Added the infinitary collapse sequence.
   - **Theorem 5.10** (`thm:infinitary-collapse`): any governance-relevant infinitary appeal must
     collapse to a finite same-domain witness.
   - **Corollary 5.11** (`cor:no-infinitary-standing-gain`): no same-domain infinitary standing gain.
   - **Theorem 5.13** (`thm:no-primitive-infinitary`): no primitive infinitary standing acts.

3. Added **Theorem 5.14** (`thm:extension-trichotomy`).
   - same-scope richer-theory rescue now falls into exactly one of:
     - definitional/bookkeeping only,
     - explicit scope change,
     - inadmissible same-domain authority import.

4. Added **Theorem 5.15** (`thm:rescue-exhaustion`).
   - semantic, infinitary, and extension rescue routes are now finitely exhausted in-paper before
     the main theorem.

5. Updated the main theorem layer accordingly.
   - **Theorem 6.2** (`thm:translation-filter`) now cites rescue-route exhaustion explicitly.
   - **Theorem 6.3** (`thm:main`) now depends on rescue-route exhaustion rather than on the former
     compressed proposition.

6. Updated the audit trail, referee reading path, abstract language, and concluding summary so the
   Phase VI sequence is visible in the proof spine.
