# Re-charge proofs for the output-length cost model

Your rows are listed in `batches/output-length/slice_{{SLICE}}.jsonl`, one JSON
object per line. Each names a proof that already verifies under the old cost
model. You produce a copy that verifies under the new one.

## What changed (2026-10-07)

Integer arithmetic still costs `1` however large the value. Producing text now
costs one step per character:

| operation | old charge | new charge |
|---|---|---|
| `IntToString(x)` | `1`, and its length treated as `1` | `Digits(x)` |
| `Join(parts, sep)` | `SumLen(parts) + \|parts\|` | unchanged; `SumLen` now exists |
| `JoinInts(xs, sep)` | `\|xs\|` in practice | `SumDigits(xs) + \|xs\|` |

`Digits`, `SumLen` and `SumDigits` are ghost functions in `prelude.dfy`. Use
them; do not define your own. A proof that defined its own `SumLen` may keep it
or switch to the prelude's.

**Output length is its own parameter.** Every program that prints L characters
pays L steps, so a bound of the form `steps <= f(n) + c * |output|` is compared
with the label through `f(n)` only. Link charges to the output with:

```dafny
IntToStringDigits(x);   // |IntToString(x)| == Digits(x)
JoinLen(parts, sep);    // |Join(parts, sep)| == SumLen(parts) + (|parts| - 1) * |sep|   (|parts| >= 1)
JoinIntsLen(xs, sep);   // |JoinInts(xs, sep)| == SumDigits(xs) + (|xs| - 1) * |sep|      (|xs| >= 1)
DigitsMono(x, y);       // 0 <= x <= y ==> Digits(x) <= Digits(y)
```

A `Digits` charge whose string never reaches `output` (a digit sum, a string
comparison, a length test) is ordinary work: it stays in the bound as a
`Digits(...)` term and counts against the label.

## What you do, per row

A slice line may carry a `note`: read it first. It says what an earlier attempt
on that row got wrong. For a retried row, number your attempt files after the
existing ones in `<attempt_dir>`.

1. Read the row's proof (`proof` in the slice line). Do not edit it. If it
   already pays for every character it prints (a `steps` update of
   `|output|`, `|IntToString(x)|` or `|Join(...)|` after the text is built),
   record it `compliant` with the line numbers that show it, and move on: no
   attempt file.
2. Copy it to `<attempt_dir>/<sid>.1.dfy` and change its include to
   `include "../../../../prelude.dfy"`.
3. Find every `IntToString`, `Join` and `JoinInts`, and every `steps` update
   that pays for one. Re-charge them per the table. Keep everything else.
4. Restate the `ensures` bound. Prefer `old f(n) + c * |output|`; use a
   `Digits` or `SumDigits` term only where the text does not reach `output`.
   Helpers that return text the caller prints may need an `ensures` relating
   their `steps` to the length of what they return.
5. `timeout 300 dafny verify <file>`, as its own command, with no time-limit
   flag: that is how the `proofs.py` gate runs it. Next attempt: copy to `<sid>.<n+1>.dfy` and edit the copy. Never
   overwrite or delete an attempt file.

## Rules

1. **Charges only.** You may change `steps` updates, ghost declarations,
   `ensures`, invariants, `assert`s and lemma calls. Executable code stays
   byte-identical: the audit compiles your file and the original row to Python
   and compares them.
2. No `assume`. No `decreases *`. Never add or change a `requires`.
3. Do not touch `solutions*/`, `prelude.dfy`, `proofs.py`, `data/`, or any
   other row's files. Do not read `batches/` other than your slice and this
   brief.
4. Some proofs carry a `requires` their row lacks. Leave it exactly as it is;
   the audit reports it separately.
5. If the re-charged bound is in a different class from the label in a way the
   output rule does not absorb, keep the proof and say so; never weaken it.

Keep any helper script or scratch file under
`batches/output-length/work/{{SLICE}}/`. Never write to `/tmp` or a shared
scratchpad: other agents run at the same time and use the same names.

## Budget — hard

Work **one row at a time**, and run one `dafny` at a time: parallel runs load
the machine, and a loaded machine turns borderline proofs into timeouts.

3 attempts and 5 minutes per row, from your first command on that row. Run
`date +%s` at the start and end of each row. Out of budget: record the row
`unresolved`; your attempt files are the record.

## What to write back

Append one JSON line per row to `batches/output-length/traj_{{SLICE}}.jsonl`
**as soon as that row finishes**:

```json
{"solution_id":"2225_120","label":"O(n)","outcome":"migrated",
 "old_bound":"4 * n + |output| + 8","new_bound":"4 * n + 2 * |output| + 8",
 "output_term":true,"relation":"confirms","old_relation":"confirms",
 "relation_reason":"",
 "charges":"IntToString(cnt) in the loop charged Digits(cnt); tied to |output| by IntToStringDigits",
 "attempts":[{"n":1,"outcome":"verified","note":"","file":"2225_120.1.dfy"}],
 "seconds":95,"why_failed":null,"obstacle":null}
```

`outcome` is `migrated`, `compliant` or `unresolved`. `relation` uses the same vocabulary
as before (`confirms`, `looser-structural`, `tighter-label`, …) and is judged
with the output rule. If it differs from `old_relation`, `relation_reason` says
which charge moved it. If `old_relation` is null, leave `relation` null: judging
a label is not this batch's job. On `unresolved`, `obstacle` is one of `z3-nonlinear`,
`invariant-gap`, `budget`, `prelude-gap`, and `why_failed` names it in one
sentence. `seconds` comes from your `date +%s` readings.

Final message ≤ 6 lines: per row, outcome and new bound.
