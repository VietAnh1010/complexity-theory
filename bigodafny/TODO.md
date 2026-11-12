# TODO

Open items only. When one is done, delete it and add a line to `CHANGELOG.md`.

## Proofs

- [ ] `2496_30`: the proof adds real loop caps (`padIter < 9`, `trimIter < 20`,
      `expIter < 2`). Without them `FormatG9`'s trim loop runs once per trailing
      zero of `digits`, unbounded when a value is outside 10^-1000..10^1000 (the
      normalising loops stop at 1000). Needs a value bound on `Solve`, quoted
      from the statement, and a proof that normalisation finishes.
- [ ] The `Gcd` bounds (`1386_19`, `1386_38`, `1871_291`, `1915_158`) are
      `n * log max`, which is loose: the running gcd only shrinks, so the total
      is `O(n + log max)`. Optional.
- [ ] `1180_626`, `2913_309`, `2913_484`: the label is higher than the tightest
      class (`mismatch`), but the proof only reaches the label (`confirms`). A
      tighter proof would make the relation `tighter-label`.
- [ ] `1871_156` and `1972_295` time out under Z3 5.1.0
      (`batches/z3-upgrade/unresolved/`).
- [ ] `2831_71` still charges `IntToString` 1 step (`batches/output-length/`).

## Value-bounded filing

- [ ] Review the 7 rows in `batches/value-bounded-open/` that were filed from
      agent notes alone: `1263_2538`, `1332_16`, `1364_161`, `1626_179`,
      `2358_103`, `2465_212`, `342_86`.
- [ ] `1332_16` looks like a missing log-bound lemma, not `value-to-size`.
- [ ] `810_131` and `1948_388` are in `value-bounded/` but marked
      `looser-translation`; that directory takes only `looser-structural`.
      Keep them or move them out.

## Data

- [ ] `dataset.py` gives the 6 `unvalidatable` rows `dafny_status:
      untranslated`, though they are translated.

## Labels

- [ ] `label_audit.py apply` only finds rows in `solutions/`,
      `solutions-disputed/` and `solutions-unsure/`. Auditing
      `solutions-unscreened/` needs it extended.
- [ ] `label_audit.py siblings` lists 87 candidate pairs over 157 rows. 109 of
      them are quarantined for `sibling-convergence` in
      `solutions-unscreened/` and were never label-audited. Review the pairs.
- [ ] `2381_156`: its `O(1)` label and `ok` verdict (r3) predate the 2026-10-07
      `IntToString` charge. Its proof bounds `2 * Digits(n) + 4`, and arms agents
      proved `Digits(n)**2` bounds over the `Power` helper. Re-audit; if the label
      changes, update `fuzzing/experiments/arms/manifest.jsonl` and re-judge.

## Gates (an agent must not change a gate that judges its own work)

- [ ] `audit.py` does not flag runs over budget. Known ones: `2128_34`
      (4 attempts, 480 s), `1582_118` and `2254_6` (4 attempts), `2704_92`
      (1,500 s), `2231_77` (420 s).
- [ ] `2254_6` and `2128_34` count as proved in campaign 1 though over budget.
      Decide whether to count them as unresolved.
- [ ] `data/constraints.jsonl` covers 5 problems (1501, 577, 827, 1254, 1276).
      The other 306 count every test; transcribe their limits to find more bogus
      tests.

## Tooling

- [ ] Deferred: make `bigodafny/` an installed package (`pyproject.toml`, `pip install -e .`).
      Import by package name (`bigodafny.common`), drop every `sys.path.insert`, and run
      tools by `-m` or entry points. Until then a module named like `common.py` beside a
      script shadows `bigodafny/common.py`. Touches every script, the docs, the skills and
      the `blind-guess` hook; re-run every gate after it.
