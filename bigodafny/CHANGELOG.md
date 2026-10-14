# Changelog

What changed in the corpus, its rules, or its tools, newest first. One bullet
per change. State documents (`CLAUDE.md`, `DOCS.md`, `COMPLEXITY.md`, the
`solutions*/README.md` files, the skills) describe only the present; when a
change lands, update them and add a bullet here.

A campaign's own run record stays in `batches/<campaign>/README.md`. Superseded
data lines go to `old-record.jsonl` beside the file they came from.

## 2026-10-14

- Input and output each count once and are excluded from the class, like
  `|output|` (`COMPLEXITY.md`). One read: find each token's boundaries, then
  convert it (a numeral in any base, prelude or hand-written); one write:
  format, assemble, `Join`. Any further pass is work. `ParseInt` and `SplitWs`
  cost `|s|`. Eight proofs that charged parsing as a constant or not at all
  are re-charged (`2015_175`, `2105_248`, `2105_521`, `2217_247`, `378_91`,
  `976_1131`, `2942_42`, `2942_55`); the audit prompt follows, `IntToString`
  at its digit count included.
- Verdicts re-filed under that rule (`batches/labelaudit/verdicts_io-rule*.jsonl`):
  `378_91`, `976_1131`, `966_134`, `2854_30`, `1047_26` to `solutions/`;
  `378_20` to `solutions-disputed/` (`O(n*m)` label, `O(n)` code); `1047_641`
  re-filed as `other` (a second boundary scan, a prepend-built column).
- Tests outside a limit the problem statement sets are bogus: the test gates,
  `baseline.py` and `precheck.py` skip them and record the count. Limits live
  in `data/constraints.jsonl`, quoted from the statement: 1501, 577, 827,
  1254, 1276. 48 of 1501's 122 tests reach `k = 10^12` against `k <= 10000`;
  both 1501 rows turn `strict` and `1501_224` passes 74/74, leaving
  `solutions-ungateable/`. 18 of 1276's generated tests break its limits.
- `precheck.py` has Dafny evaluate each `requires`: one compiled method per
  clause, built with `dafny translate py` and run on every stored input. The
  Dafny-to-Python translation is gone. `--all` covers every row with a
  `requires` and every recorded row; a `{:attr} Solve(` header is found.
  Full run: 848 clauses over 307 rows, 0 violated, 0 unchecked; 197 of those
  rows had never been checked.
- No `var` binding inside a `requires` (`CLAUDE.md`, verify and translate
  skills). `85_71`'s clause is now `exists k :: ... d_list[k] == 1`;
  `1039_15`'s is written without `var`.
- `2742_0` re-proved without the `requires N == |values|` its proof copy had
  added, false on every real input; same bound.
- `1738_180` stops its inner scan at the first match, as Python's `in` does;
  its one timeout is gone, 32/32.
- The nine rows with their own `ParseInt`/`ParseIntFrom` (and four proof
  copies) use the prelude's, which now ensures a non-negative result unless
  the text starts with `-`; the `1039` files use `ParseInts`. Seven proofs
  drop local copies of `SumLen`/`SumLenSnoc`, now in the prelude.
- `validate.py` and `proofs.py` check rows in parallel; every gate's
  `--workers` defaults to `common.WORKERS` (8). Both re-check a failure alone
  before recording it: load timed out `1582_118`, `2913_309`, `577_509` and
  `1738_180`, and all pass alone.
- `common.write_jsonl(..., key=)` archives every replaced or dropped line in
  `old-record.jsonl`; every `data/` record writer passes its key.
- `GcdStepsBound`, `GcdStepsBoundFirst` and `GcdLeFirst` did not verify under
  Z3 5.1.0, unnoticed because `dafny verify` skips included files. Fixed with
  `SmallMod` and `ModUpper`; `proofs.py` now verifies the prelude.
- The cloud environment runs Z3 5.1.0, matching the local pin.
- The bigodafny skill no longer carries counts (they live in `STATUS.md`), and
  drops a finding fixed on 2026-10-13 (gates testing a row's proof copy).
- `dataset.py` stops on a missing `numpy` instead of marking every row
  `unvalidatable`. The bigodafny skill's state check activates `.venv`.

## 2026-10-13

- `data/quarantine.jsonl` restored to all 127 `solutions-unscreened/` rows. A
  2026-09-07 run (`a56cfcf`) rewrote it with only its 12 new entries, dropping
  115 rows' reasons while the rows stayed quarantined; the reasons are merged
  back from the file's three committed versions. `dataset.jsonl` and
  `stats.json` re-derived: only the quarantine fields changed.
- `validate.py` and `difftest.py` no longer search `solutions-proved/`: they
  found a row's proof copy before the row itself when the row sat in
  `solutions-disputed/`, `solutions-unsure/` or `solutions-ungateable/`, so
  those rows were tested through the copy. 11 loose rows re-run (all agree);
  `validate.py` re-run in full.
- Docs: glossary limited to terms this project defines; gate definition
  corrected, with the directories each gate covers; `verify_all.py` does not
  sweep `solutions-disputed/` or `solutions-unscreened/`; `TODO.md` content no
  longer copied into other docs (`CLAUDE.md` § Counts).
- `STATUS.md`: every corpus count in one file, checked against `data/`. Other
  docs no longer carry counts (`CLAUDE.md` rule). Corrected on the way:
  `validate.py` has 1 failing row (`1738_180`), not 7; the 6 `unvalidatable`
  rows are not run.
- Docs rewritten in plainer words (`DOCS.md`, `README.md`, `CLAUDE.md`,
  `COMPLEXITY.md`, `TODO.md`, every `solutions*/README.md`, `batches/README.md`,
  `CAMPAIGN_CONFIG.md`). Stale facts fixed: `signature.py` maps all 311
  problems; `apply` cannot yet move `solutions-unscreened/` rows; the partition
  has seven directories; `solutions-proved/README.md` lists all three proofs
  that compile to different Python; the `§ 1` links to `COMPLEXITY.md`.
- Docs: a glossary in `DOCS.md`; proof relations defined in `COMPLEXITY.md`.
  Counts corrected against `data/`: proved labels `O(nlogn)` 67 and `O(logn)` 1;
  disputed causes (34 `translation`, 1 blank) and confidence (101/96/5); the
  `1950` rows do carry label verdicts.
- `selftest.py` folded into `validate.py --self-test`; `checkverdicts.py`
  into `label_audit.py check`, which `apply` now runs first and refuses on.
  Dropped `checkverdicts.py`'s proof cross-check: it printed proved bounds and
  rejected nothing, though three docs said it rejected contradicting verdicts.
- `batches/labelaudit/`: the 62 per-batch verdict files merged into one per
  round, in the order applied: `verdicts_r1-r2.jsonl`, `verdicts_r3.jsonl`
  (with `r3_fix`, `r3d_*`, overrides), `verdicts_r4.jsonl` (with `r4d`, `r4s`,
  `r4u`, overrides). `auditor` still names each line's batch. The last line
  per row matches `data/label_audit.jsonl` for all 506 rows. Dropped
  `verdicts_r2.jsonl` (80 lines identical to `verdicts_01`–`04`) and
  `old-PROMPT.md`. File names in the bullets below are the pre-merge names.
- `callgraph.py` writes `out/call_depth.jsonl` (git-ignored) and drops its
  partial-run guard; `collect.py` reads it from there. `data/call_depth.jsonl`
  removed: only the artifact payload read it.
- Removed code only `experiments/` used: `score()`, `difficulty_static()`,
  `drift()` and its append helpers from `features.py`; the unused `EXPORT`
  from `dataset.py`. `experiments/` is archived: `aggregate.py` no longer
  imports; `select.py` already did not.
- Removed `common.event()` and `data/events.jsonl`: a per-run summary log no
  script or doc read. The two warnings only it carried (`extract.py` rows with
  missing fields, `signature.py` dataclasses that differ within a problem) now
  go to stderr. Unused imports dropped across the scripts.
- Scratch output moved to `out/`: `validate.py` spot checks
  (`out/<prefix>validation.jsonl`), `difftest.py`'s resume checkpoint, and
  `label_audit.py evidence` batches (`out/labelaudit/`). `.gitignore` cut from
  12 rules to 5; `evidence --only` output (`reaudit_NN.json`) was not ignored.

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
