# TODO

Open items only. Delete an item when it is done and record the change in
`CHANGELOG.md`.

## Proofs

- [ ] `2496_30`: proof adds non-ghost loop caps (`padIter < 9`, `trimIter < 20`,
      `expIter < 2`); emitted Python differs from the row. Decide: fix or drop.
- [ ] Overlay proofs that add or change a `requires` on the row's own code
      (`audit.py` lists drawn ones as `requires_changed`; includes `794_794`
      and `307_14`). Per row: prove without it, or move the precondition into
      the row through its gates.
- [ ] Overlay proofs never drawn by a campaign were never checked by `audit.py`
      for emitted Python or `requires`. Run both checks over them.
- [ ] `1359_189` and `810_131` emit Python that differs from their rows.
- [ ] The `Gcd` bounds (`1386_19`, `1386_38`, `1871_291`, `1915_158`) are loose
      (`n * log max`): the running gcd only shrinks, so the depths telescope to
      `O(n + log max)`. Optional tightening.
- [ ] `1180_626`, `2913_309`, `2913_484`: the label is above the tight class
      (`mismatch`), but the proof only reaches the label (`confirms`). A
      tighter proof would make the relation `tighter-label`.
- [ ] `1871_156` and `1972_295` time out under Z3 5.1.0
      (`batches/z3-upgrade/unresolved/`); `2831_71` still charges `IntToString`
      one step (`batches/output-length/`).

## Value-bounded filing

- [ ] Review the 7 rows in `batches/value-bounded-open/` filed from agent text
      only: `1263_2538`, `1332_16`, `1364_161`, `1626_179`, `2358_103`,
      `2465_212`, `342_86`.
- [ ] `1332_16` reads like a missing log-bound lemma, not `value-to-size`.
- [ ] `810_131` and `1948_388` are in `value-bounded/` but `looser-translation`;
      the filing rule admits only `looser-structural`. Keep or move out.

## Labels

- [ ] Decide the `ParseInt` charge: the brief charges a numeral token its
      width, the proofs charge it 1. Six `unsure` rows wait on it
      (`solutions-unsure/README.md`).
- [ ] `label_audit.py apply` handles rows in `solutions/` and
      `solutions-disputed/` only; auditing `solutions-unscreened/` needs it extended.
- [ ] `label_audit.py siblings` lists 87 candidate pairs; only the 12 rows in
      `data/quarantine.jsonl` were ever reviewed.

## Gates (not for an agent whose work they judge)

- [ ] `audit.py` does not flag budget overruns. Recorded overruns: `2128_34`
      (4 attempts, 480 s), `1582_118` and `2254_6` (4 attempts), `2704_92`
      (1,500 s), `2231_77` (420 s).
- [ ] `2254_6` and `2128_34` count as agent-proved in campaign 1 though over
      budget; decide whether to count them as unresolved.
