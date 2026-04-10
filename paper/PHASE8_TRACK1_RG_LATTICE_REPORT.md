# Phase VIII Track 1 report
## RG / lattice / cluster expansion

Scope attacked:
- one-shot entrance;
- same-scale Wilson return;
- fixed-lattice gap;
- weak-window sufficiency.

Prompt used:
Try to force the Route 1 chain to use a second weak-window certificate, a stronger same-scale Wilson return theorem than the logarithmic-depth statement actually proved, or a fixed-lattice premise that is not exported theorem-locally.

Nodes reviewed:
- core Sections `03_uv_gate.tex` and `04_route1_lattice_gap.tex`;
- proof-kernel Sections `03_uv_gate.tex`, `04_route1_lattice_gap.tex`, and `02_dependency_spine.tex`;
- Companion I guide text and the theorem-facing Route 1 proof-home summaries.

Issues logged:
- **RG-01**. Rewritten. The proof-kernel reading guide was upgraded to the four specialist tracks and now sends the first-pass audit directly to the logarithmic-depth Wilson-return theorem and the sole live weak-window certificate.
- **RG-02**. Rebutted. The frozen packet DAG and Theorem IV.4 already show that no second weak-window node enters the live public spine.

Kill criteria checked:
- no second live weak-window certificate surfaced;
- no theorem-facing Wilson-return summary regressed to fixed-depth or arbitrary-depth uniformity;
- no fixed-lattice theorem needed a stronger premise than the packet route states.

Disposition:
The Route 1 chain passes the internal hostile read. No closure-critical RG / lattice issue remains open.
