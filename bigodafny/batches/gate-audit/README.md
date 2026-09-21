# `gate-audit/` — the seven rows in `solutions/` with no passing gate result

`prove-sample-2`'s sampler kept seven rows out of its pool because the latest
recorded gate result for each was negative or missing. This is what they turned
out to be.

The question the gates cannot answer on their own: **when `validate.py` says
`fail`, is the translation wrong, or is the harness?** `control.py` answers it
by running the ORIGINAL PYTHON through the same `Input.from_str` round-trip the
Dafny gets. Three outcomes, and only the third is the translation's fault:

| verdict | meaning |
|---|---|
| `unparseable` | `from_str` raised; neither implementation can be run on that test |
| `python-fails` | the round-trip parsed but destroyed information the solution reads |
| `python-ok` | the test survives; a Dafny failure here is real |

## Result

| row | stored | runnable | Dafny | verdict |
|---|---|---|---|---|
| `1196_100` | 12 | 10 | 10 | **gate exempt** |
| `1196_51` | 12 | 10 | 10 | **gate exempt** |
| `1578_481` | 8 | 1 | 1 | **gate exempt** |
| `1578_724` | 8 | 1 | 1 | **gate exempt** |
| `1950_45` | 42 | 23 | 7 | moved to `solutions-disputed/` |
| `1950_47` | 42 | 23 | 19 | moved to `solutions-disputed/` |
| `1501_224` | — | — | — | loose tier, see below |

**Four of the six strict rows pass every test that can be run.** Their `fail`
is entirely produced by BigOBench's own data:

- **1578** — `Input.from_str` asserts `all(n == len(line) for line in matrix)`,
  but this problem's rows always hold exactly 3 columns. Every test with
  `n != 3` is rejected before either implementation runs. 7 of 8 tests die
  there; the one survivor is the public test, where `n` happens to be 3.
- **1196** — two stored tests declare `n = 4` and then supply three text lines,
  so `assert len(text_list) == n` fails.

They stay in `solutions/`, each carrying a `GATE EXEMPT` header, recorded in
`data/gate_exempt.jsonl`. **`validate.py` was not modified.** A gate may not be
edited by the work it judges, and making four rows pass by relaxing the gate is
the exact shape of that mistake. The gate still reports `fail`; the record says
why that reading is wrong.

## The two `1950` rows are different

Their dataclass types the coefficient as `float`, and the inputs carry up to
100 significant digits. 19 of 42 stored tests do not survive
`str(float(c)) + 'e' + str(int(e))` — the **original Python fails them too**
once routed through the dataclass. So no translation can ever exceed **23/42**
on these rows.

But the Dafny passes only 7 and 19 of those 23, so on top of the harness defect
there are at least 16 and 4 genuine failures. Both translations cap the
fractional part at 12 digits where the Python uses `Decimal`, which keeps the
input's own precision.

Moved to `solutions-disputed/` with a `TRANSLATION AUDIT` header. That
directory is the project's review queue and its README says every gate still
runs on what sits there; what is disputed here is the code, not the label. To
come back they need 23/23 on the runnable tests plus a `gate_exempt` entry for
the other 19.

## `1501_224`

The loose-tier row, whose recorded `difftest.py` status is `differs`: 77 of 93
comparable tests agree, 29 are `python-failed`, and **16 are timeouts — not
disagreements**. Zero tests where the two implementations produce different
answers.

A re-measurement is running; the numbers above are the stored record, not a
fresh run. The first attempt was killed by its own 30-minute wrapper before it
wrote anything, so nothing here has been re-measured yet.

What `differs`-by-timeout-only should mean was already an open question in
`collect.py`. It is a question about the gate's status vocabulary, not about
this row, and it is left open.

## Files

| file | what it is |
|---|---|
| `control.py` | the Python-through-the-dataclass control; reads only |
| `control.jsonl` | its per-row tally and per-test detail |
| `difftest_1501_224.json` | the re-measured loose-tier result, once it lands |
