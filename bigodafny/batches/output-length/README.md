# `output-length` — re-charging proofs for one step per output character

Branch `claude/cost-model-output-length`, 2026-10-07. Not merged. Run under
Dafny 4.11.0 with Z3 5.1.0 (see `../z3-upgrade/`).

## What changed

| | before | after |
|---|---|---|
| `IntToString(x)` | `1`, result length taken as `1` | `Digits(x)` |
| `Join(parts, sep)` | `SumLen(parts) + \|parts\|`, `SumLen` defined nowhere | same, `SumLen` in the prelude |
| `JoinInts(xs, sep)` | `\|xs\|` in practice | `SumDigits(xs) + \|xs\|` |
| an additive `c * \|output\|` term | n/a | never counts against the label |

Integer arithmetic still costs `1`. `COMPLEXITY.md` § "Decisions that often
cause confusion" is the rule; the prelude adds `Digits`, `SumLen`, `SumDigits`,
`IntToStringDigits`, `DigitsMono`, `JoinLen`, `SumLenIntStrings`, `JoinIntsLen`.

## Layout

| path | what |
|---|---|
| `PROMPT.md` | the migration agent's brief |
| `attempts/<pid>/<sid>.<n>.dfy` | every attempt that differs from the promoted proof |
| `traj.jsonl` | one record per row, written by the agents; pilot, main, fixup slices in order |
| `audit.jsonl` | the promotion audit of each record, same order |
| `transcripts/{pilot,main,fixup}.jsonl` | the agent runs' transcripts, slimmed to messages, tool calls and results; one file per phase, runs in slice order, each opening with "Your slice is `<slice>`" |

A promoted row's new proof sits at its old path in `solutions-proved/`. Its
superseded records go to `old-record.jsonl` beside the file they came from:
`data/` for `complexity_proofs.jsonl`, the campaign directory for
`label_relation.jsonl` and `traj_*.jsonl`. The rewritten records carry a
`revision` block; campaign trajectories keep `agent_bound`/`agent_relation`.

## Triage at the start

| pattern | proofs |
|---|---:|
| `output := IntToString(x)` once, at the end | 167 |
| calls `Join` or `JoinInts` | 56 |
| `IntToString` inside a loop | 38 |
| a few top-level calls | 7 |
| **total producing text** | **268 / 323** |

## Result — every text-producing proof, 2026-10-07

| outcome | proofs |
|---|---:|
| promoted: re-charged, audited, moved into `solutions-proved/` | 239 |
| compliant: already paid per character; file unchanged | 26 |
| unresolved: old proof stays (`2831_71`, invariant-gap after a sort) | 1 |
| not attempted: no verifying proof to start from (`1871_156`, `1972_295`, see `../z3-upgrade/`) | 2 |
| **total** | **268** |

- 32 agent runs: pilot (3 slices), main (26 slices of 9–10), fixup (3 slices:
  the 10 rows repaired for Z3 5.1.0 that print text, plus 5 retries).
- Attempts among promoted rows: 232 on the first, 6 on the second, 1 on the third.
- 237 of the 239 new bounds are the old bound plus a `c * |output|` term.
- **No label relation changed for a reason the output rule produced.** Two agent
  relations were wrong and were corrected by hand: `2381_156`
  (agent `tighter-label`, normalised to `looser-structural`: the Python walks
  `str(n)` digit by digit, `Digits(n)` work the O(1) label omits) and
  `2803_133` (agent recorded `confirms` while reporting it unchanged; reviewed
  `tighter-costmodel` restored). Both keep the agent's claim as
  `agent_said_relation`.
- `proofs.py` after the batch: **321 / 323 verify** under Z3 5.1.0; the two
  that do not are the unresolved Z3 repairs. They moved to
  `../z3-upgrade/unresolved/` on 2026-10-08, leaving 321 / 321.
- Five promoted rows (`514_140`, `1029_92`, `1029_119`, `2942_55`, `305_284`)
  were re-translated by the remote re-audit r4 the same week. Their proofs now
  carry the new code, re-charged by hand when the two lines of work were merged.
- A superseded proof is the committed version at `7d2c8d5`, or for the seven
  Z3-repaired rows the `../z3-upgrade/attempts/` file `old-record.jsonl` names.

### What the audit rejected, and why

| row | first result | fixed by |
|---|---|---|
| `276_610`, `1180_626` | the agent introduced a non-ghost `var`; compiled Python differed | retry with `ghost var` |
| `2880_19` | no new charge; `Join` charged `\|parts\|`, not `SumLen + \|parts\|` | retry, re-charged |
| `1333_58` | three solver timeouts | retry with `{:isolate_assertions}` |

The promotion audit accepted two differences from the row only when the current proof
already has exactly the same one: a `requires` the row lacks (46 proofs), and an
emitted-Python difference (`1254_187`'s non-ghost copy of a local, since fixed). Both
are pre-existing defects, reported below, not introduced here.

### Compliant rows that were judgement calls

- `1018_254` charges `4 * |lines|` for the Join; an invariant bounds each part
  at 3 characters ("Yes"/"No"), so it covers `SumLen + |lines|`.
- `2183_2` charges each `IntToString` 1; the Join's `SumLen` pays every
  character, so the total is within a factor 2.

### Process changes made during the run

Agents work one row and one `dafny` at a time (parallel runs turned borderline
proofs into timeouts and made `seconds` meaningless); keep scratch files in
`work/<slice>/` (agents sharing `/tmp` overwrote each other's helpers); leave a
null relation null; verify with no time-limit flag, exactly as `proofs.py`
does. The agents' scratch directory `work/` was deleted after the run.

## Pilot — 10 rows, seed 20261007, 3 Sonnet agents

| row | pattern | old bound → new bound | relation | result |
|---|---|---|---|---|
| 2051_25 | single-final | `6*\|numbers\|+5` → `+ \|output\|` | confirms | promoted |
| 2522_15 | single-final | `10` → `6 + \|output\|` | confirms | promoted |
| 1333_58 | single-final | `19*n+20` → — | confirms | unresolved, z3-nonlinear; old proof kept |
| 1827_66 | join | `3*NLogN(L)+9*L+10` → `+ \|output\|` | confirms | promoted |
| 2880_19 | join | unchanged | confirms | not promoted: no new charge, and the proof adds `requires n >= 0` |
| 2926_50 | join | `8*n+500` → `+ 2*\|output\|` | confirms | not promoted: the proof adds `requires n >= 0` |
| 1915_158 | in-loop | `… + 6` → `+ \|output\|` | looser-structural | promoted |
| 2269_59 | in-loop | unchanged; `Digits` now explicit | confirms | promoted |
| 2225_120 | in-loop | unchanged | confirms | compliant as is: already charges `\|output\|` |
| 2942_55 | in-loop | `… + 10` → `+ \|output\|` | confirms | promoted |

No relation changed. Every new bound is the old one plus an `|output|` term.
`2880_19`, `2926_50` and `1333_58` were all promoted later (see above).

## Found on the way, not fixed here

- **46 of 323 proofs carry a `requires` their row does not.** Most add
  `n >= 0` or a lower bound; a few are alpha-renamed (`forall k` vs `forall i`)
  or reworded. `audit.py`'s contract check flags them, but no audit ran it over
  the whole overlay. The rule (`CLAUDE.md` § Proof restrictions) forbids it.
  (A 47th, `794_794`, was a parser bug: `requires` inside a lambda in an
  `ensures` read as a clause. Fixed in `audit.py`.)
- **`1254_187`'s proof compiled differently from its row**: `var iOld := i`
  in `Solve` was a non-ghost copy. Fixed after the batch (`ghost var`); the
  emitted Python is now identical to the row's. Nobody has run the identity
  check over the whole overlay, so others like it may exist.
- **`prelude.dfy` does not verify on `HEAD` either.** An assertion fails in
  `GcdStepsBoundFirst` and in `GcdLeFirst` (`assert a % b == a`), and
  `GcdStepsBound` times out even at 300 s. `proofs.py` runs
  `dafny verify <proof>`, which does not verify included files, so 5 proofs
  rely on those lemmas unchecked, all in `value-bounded/`: `1386_19`,
  `1386_38`, `1871_156`, `1871_291`, `1915_158`.
