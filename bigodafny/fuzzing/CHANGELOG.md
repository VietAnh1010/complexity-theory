# Changelog

Changes to `fuzzing/`'s cost charges, judging rules and tool behaviour that records depend on,
newest first.

## 2026-11-13

- `TODO.md` is gone; known issues are in `docs/08-annotate.md`, `docs/09-outputs-debugging.md`
  and `experiments/fuzz/README.md`.
- Docs trimmed of stale run counts; `experiments/arms/collect.py` drops an unused import.

## 2026-11-12

- `DafnySteps/CostModel.cs`: a prelude `ISqrt(x)` call costs `ISqrtSteps(x)` (`bigodafny/COMPLEXITY.md`).

## 2026-11-11

- `experiments/arms/`: four agent arms (`full`, `nofuzz`, `noguess`, `base`) on one stratified
  60-row manifest, each with its brief, its hook and agent type `arms-<arm>`.
- `experiments/arms/manifest.jsonl`: `1011_368` takes its corrected label `O(n**0.5)` (stratum
  `rare`) and `276_1206` its corrected `O(n)` (stratum `easy`).
- `experiments/arms/JUDGE.md`: `class_ok` accepts truth's class as a function of the inputs,
  including a sum of sizes and a tie the row enforces, as the briefs state no naming rule.
- `experiments/arms/`: every arm has a 5-minute clock; `full`'s `fuzz` calls carry
  `--time-limit 60`, which its hook requires. The hook keeps the agent from stopping while
  `result.json` names a failed run as `best_attempt`.

## 2026-10-29

- Doc 07 § Screening proofs flags a proof whose `steps / bound` at the largest bound is under
  half the ratio at 1/16 of it, not a log-log slope under 0.8; constant terms skewed the slope.

## 2026-10-28

- `fuzz` reads a proof's one top-level `ensures steps <= E`.
- `annotate` charges `var x :| x in S` 1, one step of iterating `S`; any other compiled `:|` still
  stops it.
- `deghost contracts` adds no `TraceBound` when `Solve` has no `ensures`, so `steptrace.py`
  reports no `bound_ok` for such a row.
- `fuzz.py` ends a generated input with a newline only if one of the row's stored tests ends
  with one.
- `fuzz.py --time-limit S` (default 300) skips inputs and loop reruns not started within
  S seconds and counts the inputs as `time-limit`.

## 2026-10-26

- `BRIEF.md` lists `O(n**1.5)` among the class forms, and `guard.py` accepts a `.` in a class.

## 2026-10-21

- The blind experiment only guesses the class, in modes `code` and `fuzz`.
- `BRIEF.md` fixes the form of `class` to the labels' (`O(nlogn)`, `O(n**2)`, `O(n*m)`).
- An input `data/constraints.jsonl` rejects is counted `out-of-spec`.
