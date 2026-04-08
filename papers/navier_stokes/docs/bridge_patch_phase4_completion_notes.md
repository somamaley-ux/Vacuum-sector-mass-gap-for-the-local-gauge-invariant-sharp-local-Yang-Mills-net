# Bridge-patch Phase 4 completion notes

Phase 4 clarifies the standing / endpoint-status chain so the reader sees a one-directional route

`12F -> 12G -> ST2/ST3 -> 20C.1`

rather than a restart from `12F` in isolation.

## Implemented edits
- Added an explicit dependency sentence at the start of the proof of `ST3`, identifying `12G` as the source of the fixed-scope standing packet and `12F` as scope-fixity only.
- Added an opening dependency sentence to the proof of `20C.1`, stating that endpoint-status classification is transported from the `12G` packet through `ST2` and `ST3`.
- Added a short opening sentence in the proof of `ST2` so the one-directional bridge order is visible already at the first standing/intelligibility theorem.
- Updated the front theorem map row for the standing/intelligibility packet and the compressed proof spine so the same directionality is visible before the reader reaches Part II / Part III.
- Expanded Appendix F with a dedicated Bridge-patch Phase 4 audit subsection.

## Exit condition addressed
A hostile reader should now see the standing chain as explicit and asymmetrical: `12F` classifies scope-fixity, `12G` applies `P4`, `ST2/ST3` internalize the resulting fixed-scope standing structure, and `20C.1` transports that structure into endpoint-status classification on realized periodic lineages.
