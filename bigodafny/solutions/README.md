# `solutions/` — the clean corpus

354 rows. A row is here when three things hold at once:

- **Behaviour.** `validate.py` matches its stdout against BigOBench's stored
  output (strict rows), or `difftest.py` agrees with its own Python (loose
  rows). Which gate applies is `split` in `data/dataset.jsonl`.
- **Safety.** `dafny verify` discharges every obligation the file raises with
  no user specification — sequence indices, division, termination. A row that
  cannot is in `solutions-unverified/`.
- **Label.** The label audit screened the row and its stated complexity
  describes what the Dafny costs. A row the audit disagreed with is in
  `solutions-disputed/`.

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

## Four rows here cannot be gated, and it is the harness, not the code

`dataset.py`'s `parser_ok` decides whether the harness can feed a row at all.
Four rows in this directory fail it, so neither `validate.py` nor `difftest.py`
can run on them. Their Python passes every one of its own tests and their Dafny
signature is fine — what fails is the path between the two.

| rows | why the harness cannot feed them |
|---|---|
| `1578/1578_481.dfy`, `1578/1578_724.dfy` | `Input.from_str` asserts a trailing newline the stored input does not have |
| `1950/1950_45.dfy`, `1950/1950_47.dfy` | a `real` argument carrying ~100 significant digits; Python `float()` truncates it before Dafny is called, so no implementation can pass |

Both causes were measured, and `parser_ok`'s docstring records them. What was
not recorded is that these four sit here claiming to be clean. The gate is
**inapplicable**, not failing — the same situation `solutions-untranslated/`
exists to name, arriving by a different route. Deciding whether they belong here
is open.

## Shape

    solutions/<problem_id>/<solution_id>.dfy

One method `Solve`, whose signature comes from the row's `dataclass_code` via
`signature.py`. The Python source is in the header comment, verbatim.
`data/call_depth.jsonl` records how deep each row's call chain runs — the
median row is two calls from `Solve`.
