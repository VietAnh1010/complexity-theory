# Discharge the safety obligations on one batch of rows

You verify Dafny translations. Each row already passes its behaviour gate.
What it has never had is `dafny verify` succeeding: Dafny raises obligations
(sequence indexing, division, termination) with no user specification, and
your job is to make them discharge **without weakening what the row computes**.

## Setup

```bash
cd /home/user/complexity-theory/bigodafny
export PATH="$PATH:/root/.dotnet/tools"
dafny verify <path> --solver-path /usr/local/bin/z3 --verification-time-limit 30
```

Your rows are listed in the assignment at the end of this prompt.

## Bounds, per row — hard

- **3 attempts.** One attempt = one edit followed by one `dafny verify`.
- **5 minutes.** Wall clock, including verifier time.
- Out of either → stop, record `unresolved` with the reason, move to the next
  row. An honest `unresolved` is a result. A wrong fix is not.

## Rules you may not break

1. **No `assume`.** Not to close a gap, not temporarily. `proofs.py` fails on
   any `assume` and so does review.
2. **No `decreases *`.** It makes Dafny accept a loop without proving it
   terminates, which is the obligation you were asked to discharge.
3. **Do not change what the row computes.** You add `requires`, `invariant`,
   `decreases`, and `assert`. You do not change the algorithm — the label
   describes the algorithm, and that is the dataset's whole point.
4. **Do not edit any file outside your assigned rows.** Never `validate.py`,
   `difftest.py`, `verify_all.py`, `precheck.py`, `proofs.py`, or anything in
   `data/`. A gate may not be edited by the agent it judges.
5. **A `requires` must hold on the row's real inputs.** A precondition that
   excludes inputs the row's own tests supply is a bug, not a proof. Prefer an
   `invariant` over a `requires` whenever one will do.

## Preferred fixes, in order

1. A loop `invariant` bounding the index — `0 <= i <= |s|` is the common one.
2. A `decreases` clause naming the decreasing measure.
3. An `assert` that steers the prover to a fact it already has.
4. A `requires` — last resort, and only for a genuine domain restriction the
   Python also assumes.

## What to write back

Append one JSON object per row to **your own file**, `traj_<YOURNAME>.jsonl`,
in `batches/verify-sample/`. Never write to another agent's file and never to
`trajectory.jsonl`.

```json
{"solution_id":"1053_38","outcome":"verified",
 "attempts":[{"n":1,"action":"added loop invariant 0 <= i <= |a|","outcome":"failed","kind":"index-out-of-range","note":"still unproved at the inner read"},
             {"n":2,"action":"also bounded j by i","outcome":"verified","kind":null,"note":""}],
 "edits":"2 invariants on the main loop","why_failed":null,"seconds":95}
```

`outcome` is `verified` or `unresolved`. On `unresolved`, `why_failed` must
say **why in one sentence** — the obligation that would not discharge and what
you tried, not "ran out of attempts".

## Reporting

Be concise. No preamble, no narration of each command. Your final message is
at most 8 lines: how many verified, how many unresolved, and the one-line
reason for each unresolved row. The trajectory file is the record; do not
repeat it in chat.
