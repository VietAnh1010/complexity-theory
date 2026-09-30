# TODO

Open items found while normalising on 2026-09-29. Tick a box when done.

## Proofs

- [ ] `2496_30`: proof adds non-ghost loop caps (`padIter < 9`, `trimIter < 20`,
      `expIter < 2`); emitted Python differs from the row. Decide: fix or drop.
- [ ] 47 overlay proofs add or change a `requires` on the row's own code (38 are
      drawn rows; `audit.py` lists them as `requires_changed`). Per row: prove
      without it, or move the precondition into the row through its gates.
- [ ] Includes `794_794` and `307_14`, promoted from the campaign 7 rerun.
- [ ] 31 overlay proofs were never drawn, so `audit.py` never checked their
      emitted Python or `requires`. Run both checks over them.

## Value-bounded filing

- [ ] Review the 7 rows filed in `batches/value-bounded-open/` on 2026-09-29
      from agent text only: `1263_2538`, `1332_16`, `1364_161`, `1626_179`,
      `2358_103`, `2465_212`, `342_86`.
- [ ] `1332_16` reads like a missing log-bound lemma, not `value-to-size`.
- [ ] `514_140` and `1718_1166` are `looser-structural` but not in
      `value-bounded/`; their reasons name a translation artifact and a sort,
      not an input value. Confirm they stay out.

## Gates (not for an agent whose work they judge)

- [x] Remove the `solutions-proved/nlogn/` remnants: `PROVED_NLOGN` in
      `common.py`, `proofs.py`, `precheck.py`; `tight_variant` in `collect.py`.
- [ ] `experiments/selftest_grade.py` imports `INEXACT`, `NLOGN`, `VERIFIED`,
      which `common.py` no longer defines; it fails on import.
- [x] `precheck.py` never drops a row's stale clauses when the row loses all its
      `requires` (1077_84's was removed by hand).
- [ ] `audit.py` does not flag budget overruns. Recorded overruns: `2128_34`
      (4 attempts, 480 s), `1582_118` and `2254_6` (4 attempts), `2704_92`
      (1,500 s), `2231_77` (420 s).
- [ ] `2254_6` and `2128_34` count as agent-proved in campaign 1 though over
      budget; decide whether to count them as unresolved.

## Records and docs

- [ ] `solutions-disputed/README.md` exit rule still names
      `data/gate_exempt.jsonl`, replaced by `data/gate_ungateable.jsonl` on
      2026-09-21. Restate the rule.
- [ ] `label_relation.jsonl` ad-hoc flags: `reason_rewritten` (c4),
      `redrawn_already_proved` (c5), `relation_superseded` (c1, c4), `resolved`
      (c2). Fold into the `revision` scheme; `provestats.py` reads `resolved`.
- [ ] Campaign 1 records predate `relation` and use `agrees_with_label`; the
      reviewed relation is only in `label_relation.jsonl`.
- [ ] `batches/prove-sample/explore.py` reads agent transcripts from a session
      `/tmp` path that no longer exists; it cannot be re-run.
