# `verify-sample/` — a 50-row probe of the unverified backlog

**Question.** 106 rows in `solutions/` had no `dafny verify` record. Were they
*failing*, or had the verifier simply never been run on them?

**Answer: never run.** All 50 sampled rows verify with no edit at all, and so
does the rest of `solutions/` — the full sweep came back **354 of 354**.

## How the sample was drawn

| | |
|---|---|
| frame | `solutions/`, no row in `data/verification.jsonl`, a non-empty label |
| excluded | `1196_51` — the one row in the frame that does not pass its gate |
| pool | 105 |
| drawn | 50, `random.sample`, **seed 20260916** |

Every row in the 106 carried a label, so the "no label, do not handle" rule
excluded nothing. Labels in the pool: `O(n)` 48, `O(nlogn)` 28, `O(n**2)` 17,
and a tail of 9 others.

## Result

`baseline.py` runs `dafny verify --verification-time-limit 30` on each row and
writes `baseline.jsonl`. **50 of 50 verified, zero edits, zero agent attempts.**
Neither of the two bounds — 3 attempts, 5 minutes per row — was ever reached.

**One of the 50 is verified on weaker terms.** `1675_29` carries `decreases *`,
which makes Dafny accept its loop without proving it terminates. Every other
obligation discharges; termination is opted out, not proved. Across
`solutions/` 10 rows are in that position, so the honest corpus figure is
**344 fully verified, 10 verified-except-termination**.

`trajectory.jsonl` carries one record per row in the shape the agents would
have written: attempt 0 is "file unmodified", outcome `verified`.

### The result was controlled before it was believed

50/50 is the shape a broken harness produces, so the script was checked twice:

- Three rows `data/verification.jsonl` recorded as *failing* (`1332_16`,
  `1678_68`, `457_38`) were re-run. All three verified — evidence the **record
  was stale**, not that the script is blind. `457_38` is the weak case: it was
  recorded as a termination failure and it still does not prove termination,
  it carries `decreases *`.
- An `x[5]` read on an unconstrained `seq` was injected into a copy of
  `1053_38`. The script reported `verified: false`, `index-out-of-range`. It
  detects failure.

## Why the record was stale

`data/verification.jsonl` held 362 rows and **114 of their paths no longer
existed** — those rows had moved to `solutions-disputed/` and
`solutions-unscreened/` after the label audit, and the file was never
regenerated. The remaining 248 are exactly `solutions/` minus the 106.

The file is not written per row; `verify_all.py` rewrites it whole. So the gap
was never a backlog of hard rows. It was one sweep that had not been re-run.

## Files

| file | what it is |
|---|---|
| `manifest.jsonl` | the 50 sampled rows: id, path, label, split, gate |
| `baseline.py` | attempt 0 — verify unmodified. Writes only inside this directory |
| `baseline.jsonl` | its output |
| `trajectory.jsonl` | per-row attempt record, the deliverable |
| `AGENT_PROMPT.md` | the brief for repair agents; unused on this sample, kept for the rows that do fail |

## What this closed, and what it did not

The sweep took the recorded failures in `solutions/` from 12 to **0**. Seven of
the eight rows the last brief listed as failing verify outright; `457_38` is
the eighth and it opted out of termination rather than proving it.

What remains open is not safety. It is the 10 `decreases *` rows, the label
audit over `solutions-unscreened/`, and the three decisions in `../../DOCS.md`.

`../../collect.py` reduces all of this to `data/artifact_data.json`, so a later
artifact renders measured numbers instead of transcribed ones.
