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
- [ ] Campaign 1's first audit (2026-09-30): `1359_189` and `810_131` emit
      Python that differs from their rows.
- [ ] Five proofs charge each `Gcd` call one step, against the charge table's
      helper rule: `1386_19`, `1386_38`, `1871_156`, `1871_291`, `1915_158`.
      Re-prove with Euclid's depth charged, or add a gcd exception to the table.
- [ ] `2942_55`: the translation adds a 2009-slot table the Python's dict lacks;
      that literal bounds the `2**m` loop, so the O(n) bound hides a value term.
- [ ] `305_284`: the translation replaces the Python's `for x in range(p, q)`
      search with a closed form (CLAUDE.md: preserve the algorithm).
- [ ] `810_131` and `1948_388`: the looser term comes from the translation (no
      float `sqrt`), not the Python; the vocabulary has no `looser-translation`.
- [ ] `proofs.py`'s `bound_of` captures code after the `ensures` of `2128_34`
      and `514_140`; their `proved_bound` in `complexity_proofs.jsonl` is wrong.

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
- [x] `label_relation.jsonl` ad-hoc flags: `reason_rewritten` (c4),
      `redrawn_already_proved` (c5), `relation_superseded` (c1, c4), `resolved`
      (c2). Fold into the `revision` scheme; `provestats.py` reads `resolved`.
- [x] Campaign 1 records predate `relation` and use `agrees_with_label`; the
      reviewed relation is only in `label_relation.jsonl`. Now true of every
      campaign by design: every proved row has a reviewed line there.
- [ ] `batches/prove-sample/explore.py` reads agent transcripts from a session
      `/tmp` path that no longer exists; it cannot be re-run.
