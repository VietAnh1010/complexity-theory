# TODO

Open items only. When one is done, delete it and add a line to `CHANGELOG.md`.

## Proofs

- [ ] `2496_30`: the proof adds real (non-ghost) loop caps (`padIter < 9`,
      `trimIter < 20`, `expIter < 2`), so it compiles to different Python than
      the row. Fix it or drop it.
- [ ] `1359_189` and `810_131` also compile to different Python than their rows.
- [ ] Some proofs add or change a `requires` on the row's own code. `audit.py`
      (`.claude/skills/bigodafny-prove-campaign/scripts/`)
      lists the drawn ones as `requires_changed`, including `794_794` and
      `307_14`. For each: prove it without the `requires`, or add the
      `requires` to the row and re-run the row's gates.
- [ ] Proofs no campaign drew were never checked by `audit.py`, for either the
      compiled Python or `requires`. Run both checks on them.
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

- [ ] Decide what `ParseInt` costs. The audit prompt charges a number its digit
      count; the proofs charge it 1. Six `unsure` rows wait on this
      (`solutions-unsure/README.md`).
- [ ] `label_audit.py apply` only finds rows in `solutions/`,
      `solutions-disputed/` and `solutions-unsure/`. Auditing
      `solutions-unscreened/` needs it extended.
- [ ] `label_audit.py siblings` lists 87 candidate pairs over 157 rows. 109 of
      them are quarantined for `sibling-convergence` in
      `solutions-unscreened/` and were never label-audited. Review the pairs.

## Gates (an agent must not change a gate that judges its own work)

- [ ] `audit.py` does not flag runs over budget. Known ones: `2128_34`
      (4 attempts, 480 s), `1582_118` and `2254_6` (4 attempts), `2704_92`
      (1,500 s), `2231_77` (420 s).
- [ ] `2254_6` and `2128_34` count as proved in campaign 1 though over budget.
      Decide whether to count them as unresolved.
- [ ] `1501_224` (`solutions-ungateable/`): `difftest.py --loose` re-runs it
      every time, about 39 minutes of timeouts for a result that cannot change.
      Refresh its record once (`difftest.py --only 1501_224`; the stored one
      predates the 2026-10-08 run), then skip `solutions-ungateable/` as
      `validate.py` does. Needs the user's go-ahead.

## Environment

- [ ] The cloud environment still runs Z3 4.12.1. Upgrade it to 5.1.0, or its
      proof runs will disagree with local ones.
