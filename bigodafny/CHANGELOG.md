# Changelog

Changes to the rules, the cost model and the gates, newest first. Records follow the rules of
their day: check a record's date here before reusing it. State documents (`CLAUDE.md`, `DOCS.md`,
`COMPLEXITY.md`, the `solutions*/README.md` files, the skills) describe only the present; when a
rule changes, update them and add a dated bullet here.

A campaign's own run record stays in `batches/<campaign>/README.md`. Superseded data lines go to
`old-record.jsonl` beside the file they came from.

## 2026-11-13

- `batches/value-bounded-open/` is gone: every row it listed has a proof. An unproved
  value-bounded row stays open with obstacle `value-to-size`.
- Agent proof campaigns stopped after `prove-disputed-5`; known defects are in `STATUS.md`
  § Known issues.
- The translate skill states how to keep the Python's algorithm (sort, map, heap, bisect, `ISqrt`).
- `proofs.py` keeps a verified proof's record when its `fingerprint` (proof, row, prelude, Dafny
  and Z3 versions) is unchanged; `--all` re-verifies every proof.
- `bigodafny-prove-campaign`: `sample.py --dir` draws from another status directory;
  `PROMPT_disputed.md`, appended to the brief for `solutions-disputed/` rows, asks for the tightest bound.

## 2026-11-12

- `dataset.py` gives each row `blockers` and `clean`; `stats.json` counts them. A row is clean when
  it has no blocker (`STATUS.md` § Clean rows).
- `verify_all.py` sweeps every status directory except `solutions-untranslated/`. `--move` moves
  only `solutions/` rows, so a disputed or unscreened row keeps its directory. It ignores
  `decreases *` inside comments.
- `proofs.py` records `same_python` and `requires_changed` (on `Solve`) for every proof, and fails
  when a proof changes its row; `dataset.py` adds blocker `proof-changes-row`.
- `prelude.dfy`: `ISqrt` is compiled, and a call costs `ISqrtSteps(x)`, bounded by
  `ISqrtStepsBound` (`COMPLEXITY.md`).
- A row leaving `solutions-unverified/` goes to `solutions/` only with label verdict `ok`, else to
  `solutions-unscreened/`.

## 2026-11-02

- Obstacle codes are defined only in `vocab.py`. A later change to a row is a new dated line, not
  a rewrite.

## 2026-10-28

- A proof states its bound as one top-level `ensures steps <= E`, `E` over `Solve`'s inputs
  and `|output|` (`COMPLEXITY.md` § What a proof means; the `bigodafny-prove` skill).
- `COMPLEXITY.md` charges `var x :| x in s` 1, one step of set iteration, as `annotate` does.

## 2026-10-20

- A label a proof shows wrong is corrected in `data/label_corrections.jsonl`
  (BigOBench's label, the corrected one, the proof, its bound). `dataset.py`
  publishes `label` (corrected, else BigOBench's) and `label_corrected`;
  `time_complexity_inferred` stays BigOBench's. `label_audit.py` accepts the
  class `O(sqrt(n))`.
- The prelude has `ISqrt(x)` (floor square root) with `ISqrtSpec` and `LeISqrt`, for bounds of
  loops that stop once a square passes a value.

## 2026-10-16

- A function the row defines costs its cost function `F_steps`: same
  parameters, `requires` and `decreases`, body the cost of `F`'s body
  (`COMPLEXITY.md`). Replaces "recursive sequence/string helpers: argument
  length". For a helper that recurses once per element with constant work,
  argument length is within a constant factor of `F_steps`.
- `seq(n, f)` costs `n` plus each `f(i)`'s cost (`COMPLEXITY.md`).
- `COMPLEXITY.md` charges arrays (`new T[n]` costs `n`), `let` and lambdas.

## 2026-10-14

- Input and output each count once and are excluded from the class, like
  `|output|` (`COMPLEXITY.md`). One read: find each token's boundaries, then
  convert it (a numeral in any base, prelude or hand-written); one write:
  format, assemble, `Join`. Any further pass is work. `ParseInt` and `SplitWs`
  cost `|s|`. Label verdicts re-filed under this rule are in
  `batches/labelaudit/verdicts_io-rule*.jsonl`.
- Tests outside a limit the problem statement sets are bogus: the test gates,
  `baseline.py` and `precheck.py` skip them and record the count. Limits live
  in `data/constraints.jsonl`, quoted from the statement.
- `precheck.py` has Dafny evaluate each `requires`: one compiled method per
  clause, built with `dafny translate py` and run on every stored input.
- No `var` binding inside a `requires` (`CLAUDE.md`, verify and translate skills).
- `validate.py` and `proofs.py` re-check a failure alone before recording it.
- `common.write_jsonl(..., key=)` archives every replaced or dropped line in
  `old-record.jsonl`; every `data/` record writer passes its key.
- `proofs.py` verifies the prelude: `dafny verify` skips included files.
- `dataset.py` stops on a missing `numpy` instead of marking every row `unvalidatable`.

## 2026-10-13

- `validate.py` and `difftest.py` test the row, never its copy in `solutions-proved/`.
- Counts live only in `STATUS.md` (`CLAUDE.md` § Counts).
- `label_audit.py apply` runs `label_audit.py check` first and refuses a malformed verdict file.
- `validate.py` spot checks write `out/<prefix>validation.jsonl`, and `label_audit.py evidence`
  writes `out/labelaudit/` (`batches/README.md` § The `--only` trap).

## 2026-10-08

- Delete one-off scripts when the task is done (`CLAUDE.md`).
- Generated files nothing reads back go to `out/` (git-ignored, `common.OUT`).
- `label_audit.py siblings` scans every status directory.
- `proofs.py`'s corpus `assume` scan ignores `//` comments.
- A proof attempt identical to its promoted proof is deleted; every attempt that differs is kept.

## 2026-10-07

- Output costs one step per character. `IntToString(x)` costs `Digits(x)`;
  `JoinInts(xs, sep)` costs `SumDigits(xs) + |xs|`; an additive `|output|` term
  never counts against a label. `batches/output-length/` re-charged the proofs.
- Z3 pin moved from 4.12.1 to 5.1.0. `proofs.py` records `z3_version`. `batches/z3-upgrade/`
  repaired the proofs that timed out.

## 2026-10-01

- Naming rule: a label is the tight class and names each size it depends on.
  `O(n)` over several scanned strings and `O(n**2)` over two different sizes
  are `O(n*m)`. In `COMPLEXITY.md` and the audit brief. Label audit round r4.
- Label audit round r3: input values are cost parameters, `IntToString` costs 1, `Gcd` costs
  Euclid's depth.
- New status directory `solutions-unsure/` for rows the audit could not decide.

## 2026-09-30

- `Gcd` charged Euclid's depth (`GcdSteps`, `GcdStepsBound` in the prelude).

## 2026-09-23

- Prelude gained the sort-cost and binary-search lemmas (`SortCostNLogN`,
  `SortCostWithin`, `SearchPot`, `BisectStep`, `SearchLoopWithin`).

## 2026-09-22

- `IntToString(x)` and `|IntToString(x)|` charged 1 (reversed 2026-10-07).
- Unproved value-bounded rows go to `batches/value-bounded-open/`, not under
  `solutions-proved/value-bounded/`.

## 2026-09-21

- `data/gate_ungateable.jsonl` records the rows no gate can judge (`solutions-ungateable/`).

## 2026-09-17

- Value-versus-size convention: a loop bounded by an input value is a
  parameter of the bound, not a constant.

## 2026-09-16

- Collection costs stipulated, not measured:
  `s[i := v]`, `m[k := v]`, `s + [x]`, `s[a..b]` and set insertion cost 1.
  Records older than this charge the backend's copies.
- First label audit and first proof campaign (`prove-sample`).

## Undated

- Old records may use earlier directory names: `solutions-inexact/` is `solutions-unscreened/`,
  `solutions-tofix/` is `solutions-disputed/`, `solutions-verified/` is `solutions-proved/`.
- `Join` is linear; records that call it superlinear are wrong (the excess was constant overhead).
