# `z3-upgrade` — the corpus under Z3 5.1.0

2026-10-07. The pin in `CLAUDE.md` said Z3 4.12.1; the `z3` on `PATH` was 5.1.0
(installed 2026-09-02). Z3 5.1.0 is now the pin, and `proofs.py` records
`z3_version` on every line.

## What 5.1.0 changed

`proofs.py` twice, alone on the machine: **309 / 323** both times, the same 14
timeouts. The same 14 time out at a 120 s limit and with the pre-migration
prelude, so neither load nor the prelude caused them. The committed record had
them verified. Each changed `complexity_proofs.jsonl` line moved to
`data/old-record.jsonl` with the reason.

## Repair — 14 rows, 3 Sonnet agents, 3 attempts and 8 minutes per row

| outcome | rows | how |
|---|---:|---|
| repaired, bound and charges unchanged | 12 | `{:isolate_assertions}` alone for 7; a product lemma or an explicit sort-cost step for 5 |
| unresolved | 2 | `1871_156` (final ensures and a loop invariant still time out), `1972_295` (second loop) |

`1580_12`, `1948_388`, `2425_5`, `71_217` carry a pre-existing `requires`
their row lacks, and `1254_187` had a pre-existing non-ghost local (fixed after
the batch); the repairs left both unchanged. The 10 repaired rows that print text were then re-charged
by `../output-length/`.

## Layout

As `../output-length/`: `PROMPT.md`, `traj.jsonl` and `audit.jsonl` (slices
a, b, c in order), `attempts/`, `transcripts/`. `unresolved/` holds the two
proofs that still time out. A superseded proof is the committed version at
`7d2c8d5`; `old-record.jsonl` points there.

## Still open

The two unresolved proofs left `solutions-proved/` on 2026-10-08 for
`unresolved/`, unchanged except the include path. They verified under Z3
4.12.1 and are the starting point for a repair. `1871_156` is filed in
`../value-bounded-open/`; `1972_295`'s row stays in `solutions/`, unproved.
