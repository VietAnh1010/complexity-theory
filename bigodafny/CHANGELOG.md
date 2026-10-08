# Changelog

What changed in the corpus, its rules, or its tools, newest first. One bullet
per change. State documents (`CLAUDE.md`, `DOCS.md`, `COMPLEXITY.md`, the
`solutions*/README.md` files, the skills) describe only the present; when a
change lands, update them and add a bullet here.

A campaign's own run record stays in `batches/<campaign>/README.md`. Superseded
data lines go to `old-record.jsonl` beside the file they came from.

## 2026-10-08

- Rebased the output-length, Z3 and cleanup work onto the remote re-audit
  (below, 2026-10-01). Z3 5.1.0 stays the pin; the remote's run had used
  4.12.1, under which `1871_156` and `1972_295` still verify.
- The five re-translated proofs (`514_140`, `1029_92`, `1029_119`, `2942_55`,
  `305_284`) take the remote's code and were re-charged for output length;
  their earlier re-charges of the old code were dropped with their
  `old-record.jsonl` lines.
- Campaign records merged per row and field. Where both sides set `revision`,
  the output-length one is kept and the remote line is in the campaign's
  `old-record.jsonl`.
- `1871_156` and `1972_295` left `solutions-proved/`: their proofs time out
  under Z3 5.1.0 and the repair failed. Proofs in
  `batches/z3-upgrade/unresolved/`; `1871_156` filed in
  `batches/value-bounded-open/`. The overlay holds 321 proofs, all verifying.
- `batches/output-length/old/` and `batches/z3-upgrade/old/` dropped. A
  superseded proof is at git `7d2c8d5`, or for seven Z3-repaired rows in
  `batches/z3-upgrade/attempts/`; `old-record.jsonl` names which.
- History moved out of the state documents into this file.
- Deleted the `.txt` manifests in `batches/wave1/`–`wave7/`, `loose/`,
  `loose2/`, `verify/`–`verify3/` (in git history).
- `batches/output-length/` and `batches/z3-upgrade/`: per-slice `traj_*` and
  `audit_*` merged into one `traj.jsonl` and `audit.jsonl` each; slices,
  one-off scripts (`prep.py`, `promote.py`, `normalize.py`,
  `slim_transcripts.py`), `triage.json` and `proofs_run.log` deleted.
- New rule in `CLAUDE.md`: delete one-off scripts when the task is done.
- `bigodafny/.gitignore` now holds the project's ignore rules (moved from the
  repository root); `demo/` is ignored and `visualization/` deleted.
- New git-ignored `out/` (`common.OUT`) for generated files nothing reads back.
  Moved there: `artifact_data.json`, `prove_stats.json`, the three
  `*_summary.json`, `sibling_review.jsonl`.
- `corpusstats.py` merged into `collect.py`; `data/corpus_stats.json` deleted.
- `siblings.py` merged into `label_audit.py siblings`. It now scans every
  status directory, not only `solutions/`, and compares with `autojunk=False`,
  which made the similarity order-independent: 87 candidate pairs, all 12
  quarantined rows among them.
- Documentation sweep: `TODO.md` holds open items only; stale counts fixed
  (strict gate, call graph, `O(n*m)` rows); `DOCS.md` and the skill list
  `label_audit.py siblings` and `baseline.py --round-trip`; directory lists
  include `solutions-unsure/` and `solutions-ungateable/`; `label_audit.py`'s
  docstring describes the stipulated model.
- Full `validate.py` run on the current tree: 533 of 534 strict rows valid,
  `1738_180` fails as before, the five re-translated rows pass. The record now
  matches what a plain run produces; the 4 ungateable rows and the 2
  `unvalidatable` `1950` rows are no longer in it. Loose tier re-run: 99 rows
  unchanged, `1332_16` agrees on 44 of 44 tests.
- Python runs from a local `.venv` made with uv (git-ignored).
- `requirements.txt` names `numpy`, which every row's `Input` dataclass imports;
  no doc had listed a Python dependency. README's Z3 pin corrected to 5.1.0.
- `batches/gate-audit/control.py` merged into `baseline.py --round-trip`: the
  original Python run on inputs passed through `Input.from_str`. Same tallies
  as `control.jsonl` on its six rows.
- `dedupe.py` merged into `prove_stats.py`: the deduplicated view is computed
  from the draws it already loads; `data/campaign_dedup.json(l)` deleted.
  Figures unchanged.
- `collect.py` takes its campaign figures from `prove_stats.payload()` instead
  of recomputing them per campaign, and no longer carries hand-typed notes
  (campaign annotations, open decisions, a pinned Z3 version): 704 -> 321 lines.
- `batches/output-length/transcripts/`: 32 per-run files concatenated into
  `pilot.jsonl`, `main.jsonl`, `fixup.jsonl`.
- `features.py` moved from `experiments/` to the top level: `label_audit.py`
  and `collect.py` import it. The archived `experiments/` scripts that import
  it no longer find it.
- Deleted `batches/verify-sample/` (its question, whether unrecorded rows
  verify, is settled corpus-wide by `verify_all.py`) and the `sample` block
  `collect.py` built from it. Deleted `batches/stdlib-migration/`, a prompt
  for a migration that never ran.
- `proofs.py`'s corpus `assume` scan ignores `//` comments.
  A header comment in `514_140` had made every run exit 1.
- `provestats.py` renamed `prove_stats.py`, matching its outputs. Its
  deduplicated "carry a proof now" count reads the verified proofs instead of
  campaign records: 290, not 292.
- Attempts identical to their promoted proof deleted: 238 in
  `batches/output-length/attempts/`, 5 in `batches/z3-upgrade/attempts/`;
  45 that differ remain. Their audits' `final` fields point at
  `solutions-proved/`. The rule is now "keep every attempt that differs".

## 2026-10-07

- Output costs one step per character. `IntToString(x)` costs `Digits(x)`;
  `JoinInts(xs, sep)` costs `SumDigits(xs) + |xs|`; an additive `|output|` term
  never counts against a label. `SumLen`, `Digits`, `SumDigits` and five lemmas
  added to the prelude. 239 proofs re-charged, 26 already compliant, `2831_71`
  unresolved. `batches/output-length/`.
- Z3 pin moved from 4.12.1 to 5.1.0, the version actually installed since
  2026-09-02. `proofs.py` records `z3_version`. 14 proofs timed out; 12
  repaired with bounds unchanged, 2 not. `batches/z3-upgrade/`.

## 2026-10-01

- Naming rule: a label is the tight class and names each size it depends on.
  `O(n)` over several scanned strings and `O(n**2)` over two different sizes
  are `O(n*m)`. In `COMPLEXITY.md` and the audit brief.
- Re-audit r4 under the naming rule: 166 rows re-judged
  (`verdicts_r4*`, 8 overrides); 22 rows into `solutions-disputed/`, 4 out.
- The 157 rows already in `solutions-disputed/` re-audited under r3 with their
  old header stripped (`verdicts_r3d_*`): 138 `mismatch`, 12 released to
  `solutions/`, 6 `unsure`; one override (`1484_26`).
- New status directory `solutions-unsure/` for rows the audit could not
  decide; every gate searches it. Partition: 291 / 127 / 202 / 8 / 5 / 3 / 4.
- Five translations fixed to keep the Python's algorithm: `514_140` (`2**i`
  by squaring), `1029_92`, `1029_119`, `1332_16` (bitwise ops through `bv64`),
  `2942_55` (a map for the Python's dict); `305_284`'s search loop restored.
  `2942_55` and `305_284` re-proved in `solutions-proved/value-bounded/`.
- Label re-audit r3 of the 344 rows then in `solutions/`, under: input values
  are cost parameters, `IntToString` costs 1, `Gcd` costs Euclid's depth.
  288 `ok`, 45 `mismatch`, 11 `unsure`; the 45 moved to `solutions-disputed/`.
  Verdicts: `batches/labelaudit/verdicts_r3_*.jsonl`.

## 2026-09-30

- `Gcd` charged Euclid's depth (`GcdSteps`, `GcdStepsBound` in the prelude).
  `1386_38`, `1386_19`, `1871_156`, `1871_291`, `1915_158` re-proved with a
  log-of-value term and filed in `solutions-proved/value-bounded/`.
- The relation review of every proved row filed `2254_6` and `1580_12` in
  `value-bounded/`.
- `guard.py` hook removed from `.claude/settings.json`.

## 2026-09-29

- 19 proofs that failed `audit.py`'s same-code check fixed: non-ghost
  temporaries made ghost, the row's statements restored, bounds unchanged.
  `1077_84` rewritten on the row's recursive `Factorial`.
- Campaign 7's rerun proofs replaced `1043_358` and `794_794`; relation
  unchanged.
- Seven `value-to-size` rows from campaigns 5 and 6 filed in
  `batches/value-bounded-open/`: `1263_2538`, `1332_16`, `1364_161`,
  `1626_179`, `2358_103`, `2465_212`, `342_86`.

## 2026-09-24

- Campaign 7 rerun charged `GcdEx`'s recursion depth; `1678_68` filed in
  `value-bounded/` at `rows + 15`.
- Campaign 7's 30 rows without `reads` traces rerun with the newer prelude.

## 2026-09-23

- Prelude gained the sort-cost and binary-search lemmas (`SortCostNLogN`,
  `SortCostWithin`, `SearchPot`, `BisectStep`, `SearchLoopWithin`).
- `solutions-proved/nlogn/` removed: its base proofs became tight, so its
  copies were duplicates.
- `prove-sample-7` filed `1043_358` and `794_794` in `value-bounded/`.

## 2026-09-22

- `IntToString(x)` and `|IntToString(x)|` charged 1 (reversed 2026-10-07).
  `2381_156` and `276_610` returned to `solutions/` with a
  `LABEL AUDIT WITHDRAWN` header, left `value-bounded/`, and were re-proved
  tight: `steps <= 6` and `steps <= 24 * n + 2`.
- `prove-sample-4` had moved `276_610` to `solutions-disputed/` the same day,
  on its digit-count bound.
- `SortIsSorted` and `SortLastIsMax` added to the prelude; `2423_48` proved
  after failing in two campaigns.
- `batches/value-bounded-open/` split out of `solutions-proved/value-bounded/`:
  unproved rows no longer sit under a directory named `proved`.
- `proofs.py` changed; proof bounds normalised.

## 2026-09-21

- `data/gate_ungateable.jsonl` replaced `data/gate_exempt.jsonl`.
- `1501_224` re-measured (39 minutes); it reproduced the stored `differs`
  record. An earlier claim that it never terminates came from a `difftest.py`
  budget bug.

## 2026-09-17

- Value-versus-size convention: a loop bounded by an input value is a
  parameter of the bound, not a constant. `810_131`, `1484_26`, `2381_156`,
  `2607_90` moved to `solutions-disputed/`.

## 2026-09-16

- Collection costs stipulated, not measured (`batches/cost-axioms/PLAN.md`):
  `s[i := v]`, `m[k := v]`, `s + [x]`, `s[a..b]` and set insertion cost 1.
  Records older than this charge the backend's copies.
- `solutions-disputed/` re-filed from `batches/cost-axioms/refile_decisions.jsonl`:
  31 left, 5 joined, 3 re-classified, 178 → 152. The five that joined
  (`1622_305`, `1748_145`, `1367_88`, `2505_30`, `2854_107`) had matched their
  `O(n**2)` labels only through the old copy charge. Rows that left were
  re-gated: 26 strict `VALID`, 5 loose `agrees`.
- First label audit complete: 506 rows screened; 347 `ok`, 152 `mismatch`,
  7 `unsure` after the re-file.
- First proof campaign, `prove-sample`.

## Undated

- Renames: `solutions-inexact/` → `solutions-unscreened/`; `solutions-tofix/` →
  `solutions-disputed/` (118 of 152 rows needed a label change, not code);
  `solutions-verified/` → `solutions-proved/` (it collided with `dafny verify`,
  which checks safety); `solutions-nlogn/` → `solutions-proved/nlogn/`;
  `solution-guessed-verified/` → `experiments/proofs-blind/`.
- `Join` was recorded as superlinear; it is linear, and the excess was
  constant overhead. The bad call blocked 164 rows and cost four agent runs.
- `precheck.py` fixed with `find_all()` to check every copy of a row;
  `validate.py` and `difftest.py` still take the first hit.
