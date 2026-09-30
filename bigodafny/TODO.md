# TODO

Open items found while normalising on 2026-09-29 and 2026-09-30. Tick a box
when done.

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
- [x] Five proofs charge each `Gcd` call one step, against the charge table's
      helper rule: `1386_19`, `1386_38`, `1871_156`, `1871_291`, `1915_158`.
      Re-proved charging `GcdSteps` (prelude); all five now `looser-structural`,
      filed in `value-bounded/`.
- [ ] The five `Gcd` bounds are loose (`n * log max`): the running gcd only
      shrinks, so the depths telescope to `O(n + log max)`. Optional tightening.
- [ ] `2942_55`: the translation adds a 2009-slot table the Python's dict lacks;
      that literal bounds the `2**m` loop, so the O(n) bound hides a value term.
- [ ] `305_284`: the translation replaces the Python's `for x in range(p, q)`
      search with a closed form (CLAUDE.md: preserve the algorithm).
- [x] `810_131` and `1948_388`: the looser term comes from the translation (no
      float `sqrt`), not the Python; the vocabulary has no `looser-translation`.
      Now `looser-translation` (`vocab.py`).
- [ ] `proofs.py`'s `bound_of` captures code after the `ensures` of `2128_34`,
      `514_140` and `1871_291`; their `proved_bound` in `complexity_proofs.jsonl`
      is wrong (the records and manifest hold the right bound).

## Value-bounded filing

- [ ] Review the 7 rows filed in `batches/value-bounded-open/` on 2026-09-29
      from agent text only: `1263_2538`, `1332_16`, `1364_161`, `1626_179`,
      `2358_103`, `2465_212`, `342_86`.
- [ ] `1332_16` reads like a missing log-bound lemma, not `value-to-size`.
- [x] `514_140` is `looser-costmodel` now, so it stays out.
- [ ] `1718_1166` is `looser-structural` but not in `value-bounded/`; its reason
      names a sort, not an input value. Confirm it stays out.
- [ ] `810_131` and `1948_388` are in `value-bounded/` but `looser-translation`
      now; the filing rule admits only `looser-structural`. Keep or move out.

## Gates (not for an agent whose work they judge)

- [x] Remove the `solutions-proved/nlogn/` remnants: `PROVED_NLOGN` in
      `common.py`, `proofs.py`, `precheck.py`; `tight_variant` in `collect.py`.
- [x] `experiments/selftest_grade.py` imports `INEXACT`, `NLOGN`, `VERIFIED`,
      which `common.py` no longer defines; it fails on import. Won't fix:
      `experiments/` is archived (its README says so).
- [x] `precheck.py` never drops a row's stale clauses when the row loses all its
      `requires` (the main agent removed 1077_84's).
- [ ] `audit.py` does not flag budget overruns. Recorded overruns: `2128_34`
      (4 attempts, 480 s), `1582_118` and `2254_6` (4 attempts), `2704_92`
      (1,500 s), `2231_77` (420 s).
- [ ] `2254_6` and `2128_34` count as agent-proved in campaign 1 though over
      budget; decide whether to count them as unresolved.

## Records and docs

- [x] `solutions-disputed/README.md` exit rule still names
      `data/gate_exempt.jsonl`, replaced by `data/gate_ungateable.jsonl` on
      2026-09-21. Restated (also in the two `1950` headers and `gate-audit/`).
- [x] Six proofs cited deleted `solutions-proved/nlogn/` files; repointed.
- [x] Skills and `verify-sample/AGENT_PROMPT.md` hardcoded container paths; now
      relative, with `dafny` and `z3` taken from PATH.
- [x] `label_relation.jsonl` ad-hoc flags: `reason_rewritten` (c4),
      `redrawn_already_proved` (c5), `relation_superseded` (c1, c4), `resolved`
      (c2). Fold into the `revision` scheme; `provestats.py` reads `resolved`.
- [x] Campaign 1 records predate `relation` and use `agrees_with_label`; the
      reviewed relation is only in `label_relation.jsonl`. Now true of every
      campaign by design: every proved row has a reviewed line there.
- [ ] `batches/prove-sample/explore.py` reads agent transcripts from a session
      `/tmp` path that no longer exists; it cannot be re-run.
- [x] Revised trajectory records of `514_140`, `1948_388`, `276_610` kept their
      pre-review relation; synced with `label_relation.jsonl`.
- [x] Campaign READMEs' "revised" tables were stale; rebuilt from the records.
- [x] `value-bounded/MANIFEST.jsonl` repeated a stale `relation` for 2 rows;
      dropped (the relation lives in `label_relation.jsonl`).
- [x] 5 `value-bounded/` proofs lacked the `VALUE-BOUNDED` header; added.
- [x] Stale `proved_bound` in `label_relation.jsonl` (`354_95` held a helper's
      bound, `305_76` a superseded one, `514_140` and `2128_34` a misparse) and
      in `value-bounded/MANIFEST.jsonl` (`305_76`, `2607_90`); copied from the
      proofs.

