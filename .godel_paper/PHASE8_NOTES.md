# Phase VIII notes

Phase VIII implements the referee-proof packaging and completion controls from the hardening plan.

## What changed

### 1. Proof-force controls are now explicit in-paper
A new section, **Proof-force controls**, states in the manuscript itself that:
- all load-bearing claims appear as in-paper theorem environments,
- remarks and examples are explanatory only,
- companion papers are cited only for provenance / parallel development,
- mechanization is mentioned only as downstream corroboration, not as compensation for missing proofs.

This makes the packaging rule part of the audit edition instead of leaving it implicit.

### 2. Hostile-referee attack map added
A new section, **Hostile-referee attack map**, gives a finite objection-to-theorem ledger. Each standard objection is paired with the exact in-paper theorem(s) a referee must deny to keep that objection alive.

The map includes the standard pressure points named in the upgrade plan:
- “you redefined closure,”
- “Appendix A is just assumptions,”
- “there may be a deeper pre-boundary invariant,”
- “provability might still have a fifth internal role,”
- “representation difference might survive as a parallel structure,”
- “semantic truth / intended models can rescue the objection,”
- “reflection / ω-rules / transfinite closure escape,”
- “conservative extension can add the missing resources,”
- “ordinary PA-style undecidability threatens closure without translation,”
- “the main theorem still arrives too early.”

### 3. Audit trail expanded into a dependency ledger
The previous audit trail has been replaced by **Audit trail and dependency ledger** with four explicit columns:
- result in main body,
- immediate in-paper dependencies,
- theorem role,
- finite escape route closed.

This turns the audit table from a dependency summary into an objection-closure ledger.

### 4. Reading path tightened
The **Suggested hostile-referee reading path** now explicitly says that remarks and examples may be ignored without affecting correctness, because all proof force is carried by the theorem chain.

## Net effect

Phase VIII does not change the substantive theorem package. It changes the paper’s auditability and review posture:
- no remark or example is left looking load-bearing,
- no companion paper is left looking proof-essential,
- standard hostile objections are mapped to named theorem denials,
- the paper can now be audited from first page to main theorem as a self-contained impossibility stack.
