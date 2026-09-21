# `solutions-ungateable/` — the gate cannot reach a verdict

5 rows. Their Dafny is not known to be wrong. It is not known to be right
either, and it cannot be made known, because the evidence a gate needs is not
there to be had.

This is a different claim from every other directory. `solutions-unverified/`
says the verifier will not discharge an obligation. `solutions-disputed/` says
an audit found a mismatch. Here the **test data itself** fails, before either
implementation runs.

## The four `validate.py` rows

| row | stored | runnable | Dafny passes |
|---|---|---|---|
| `1196/1196_100.dfy` | 12 | 10 | 10 |
| `1196/1196_51.dfy` | 12 | 10 | 10 |
| `1578/1578_481.dfy` | 8 | 1 | 1 |
| `1578/1578_724.dfy` | 8 | 1 | 1 |

Every test that can be run, passes. The rest are rejected by the problem's own
`Input.from_str`, which `validate.py` must call to marshal a test into the
Dafny's parameters:

- **1578** asserts `all(n == len(line) for line in matrix)`, but this problem's
  rows always hold exactly 3 columns. Every test with `n != 3` dies there —
  7 of 8. The survivor is the public test, where `n` happens to be 3.
- **1196** has two stored tests that declare `n = 4` and then supply three text
  lines, so `assert len(text_list) == n` fails.

## The one `difftest.py` row

`1501/1501_224.dfy` is recorded `differs`. Of 122 stored tests: 29 are
`python-failed` (the row's own Python does not finish, so there is nothing to
compare against), 93 are comparable, **77 agree and 0 disagree**, and the
remaining 16 time out. `differs` is the status because `difftest.py` requires
`agree == comparable`.

Re-measured 2026-09-21 — 39 minutes for the one row — and it reproduced the
stored record exactly. The record was current, not stale.

## The pipeline's own word for four of them is `unvalidatable`

`dataset.py`'s `parser_ok` already marks the four `validate.py` rows
`unvalidatable`: it runs the problem's own `from_str` over every stored test
and fails a row when it raises, or when a `real` argument does not survive the
float round-trip. That classification predates this directory.

What it did not have was a place to put such a row. They sat in `solutions/`,
which claims the gate said yes, while `dataset.jsonl` said no gate applied.
This directory closes that gap.

`1501_224` is not `unvalidatable` — its split is `loose` and `difftest.py` can
run it. It is here for the other reason: the gate runs and cannot conclude.

## How this was established

`batches/gate-audit/control.py` runs the **original Python** through the same
`Input.from_str` round-trip the Dafny gets. A gate runs one implementation, so
it cannot tell a bad translation from a bad test; this can. For all four
`validate.py` rows the Python fails in exactly the same places.

`data/gate_ungateable.jsonl` is the per-row record. Each file repeats it in a
`GATE INAPPLICABLE` header, so a reader needs nothing else open.

## What was deliberately not done

`validate.py` and `difftest.py` were **not** modified. Loosening a gate until
these rows pass would make every other row's pass mean less. The gates still
report `fail` and `differs`; this directory records why those readings do not
mean what they appear to.

## Getting a row out

Two ways, and both are about the evidence, not the code:

1. **Repair the test data.** If BigOBench's stored tests or dataclass are
   corrected upstream, re-run the gate. A row that then passes moves to
   `solutions/`.
2. **Decide the gate's vocabulary.** `1501_224` needs no repair — it needs a
   ruling on whether a timeout counts against a row. That question is open.

A row must **never** leave by having its gate relaxed.

## Not the same as `solutions-untranslated/`

Those four rows have no body: they cannot be written. These five are written,
and four of them pass every test that exists to run. What is missing is the
evidence, not the translation.
