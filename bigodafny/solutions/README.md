# `solutions/` — the screened corpus

350 rows. **"Clean" is not the same as "every guarantee holds"**; the two
sections below name 7 rows where it does not, and safety is only partly done.
Read those before treating this directory as a certified set.

A row is here when all three hold:

- **Behaviour.** `validate.py` matches its stdout against BigOBench's stored
  output (strict rows), or `difftest.py` agrees with its own Python (loose
  rows). Which gate applies is `split` in `data/dataset.jsonl`.
- **Safety.** `dafny verify` discharges every obligation the file raises with
  no user specification — sequence indices, division, termination. A row that
  cannot is in `solutions-unverified/`.
- **Label.** The label audit screened the row and its stated complexity
  describes what the Dafny costs. A row the audit disagreed with is in
  `solutions-disputed/`.

## What actually holds, as measured

| | rows | |
|---|---|---|
| passes its own gate | 343 | 298 `valid` (strict) + 49 `agrees` (loose) |
| **cannot be gated** | 6 | the harness cannot feed them; see below |
| **fails its gate on speed** | 1 | `1501_224`, timeouts only, zero wrong answers |
| `dafny verify` clean | **350 — all of them** | 344 also prove termination; 6 carry `decreases *` |
| verdict `unsure`, not `ok` | 7 | `2254_143`, `1243_0`, `1364_161`, `1950_45`, `2282_16`, `2128_34`, `1578_724` |

Nothing here is *proved* to meet its label. That claim needs a ghost step
counter and lives in `solutions-proved/`, which holds instrumented copies of 18
of these rows.

## The containers these rows use

`seq`, `set`, `map` and `multiset`, whose costs `COMPLEXITY.md` now **stipulates**
rather than measures — `s[i := v]` is charged O(1) because that is what the
operation costs on an idealised machine, not because the Dafny Python backend
does it cheaply (it does not; it copies).

`array<T>` is not used. `batches/cost-axioms/PLAN.md` § 2 removed it: once
`seq` is axiomatised there is nothing an array buys except a second container
charged identically, differing only in backend implementation. Two rows are
exceptions and say so in a header comment:

| row | why it keeps an array |
|---|---|
| `2826/2826_42.dfy` | 10^6-entry table written in a loop; ~10^12 element copies as a `seq` |
| `2128/2128_34.dfy` | table sized by an input value up to 30000, written O(r) times per element |

Both are statements about the backend, not the cost model. Under the axioms
their `seq` and `array` forms are charged the same; what the axioms cannot do
is make the `seq` form finish, and the gates are non-negotiable.

## One row fails its gate on speed, not correctness

`1501/1501_224.dfy` reports `differs` under `difftest.py`: 93 comparable tests,
77 agree, and **16 disagreements that are all timeouts — zero wrong answers**.
Its loop runs about n/12 times and its own tests supply n up to 10^12, so the
emitted Python cannot finish inside 30s where CPython can.

The corpus has no tier for *correct but too slow to gate*, and `differs` reads
as a behavioural failure, which this is not. Left here pending a decision; see
`solutions-disputed/README.md` on the value-versus-size convention, which this
row also turns on.

## Six rows here cannot be gated, and it is the harness, not the code

`dataset.py`'s `parser_ok` decides whether the harness can feed a row at all.
All six rows the dataset calls `unvalidatable` live here, so neither
`validate.py` nor `difftest.py` can run on any of them. Their Python passes
every one of its own tests and their Dafny signature parses — what fails is the
path between the two.

| rows | why the harness cannot feed them |
|---|---|
| `1196/1196_100`, `1196/1196_51`, `1578/1578_481`, `1578/1578_724` | `Input.from_str` raises `AssertionError` on some stored inputs — it asserts a trailing newline they do not have |
| `1950/1950_45`, `1950/1950_47` | a `real` argument carrying ~100 significant digits; Python `float()` truncates it before Dafny is called, so no implementation can pass |

Both causes were measured, and `parser_ok`'s docstring records them. What was
not recorded is that all six sit here claiming to be clean. The gate is
**inapplicable**, not failing — the same situation `solutions-untranslated/`
exists to name, arriving by a different route. Whether they belong there is
open.

`1196_100` and `1196_51` were worse than ungated: they were recorded as strict
**failures** until `validate.py` learned which tier it gates. A `fail` there
measured the harness, not the translation.

## Shape

    solutions/<problem_id>/<solution_id>.dfy

One method `Solve`, whose signature comes from the row's `dataclass_code` via
`signature.py`. The Python source is in the header comment, verbatim.
`data/call_depth.jsonl` records how deep each row's call chain runs — the
median row is two calls from `Solve`.

## Four rows left on 2026-09-17

`810_131`, `1484_26`, `2381_156` and `2607_90` moved to `solutions-disputed/`.
Not because anything is wrong with them — each passes its gate, verifies, and
carries a correct proof that stays in `solutions-proved/`.

They moved because the **value-versus-size convention was decided**: a loop
bounded by an input value counts, and the value is a parameter of the bound.
`COMPLEXITY.md` § 1 is the authority. Under it, each of those four labels
omits a term the code actually pays, so the label no longer describes the row.

The translation is faithful in all four. The disagreement is with BigOBench's
label, which was fitted by profiling and assumes the opposite convention.
