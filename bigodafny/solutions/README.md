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

## One row here cannot be gated

`1501/1501_224.dfy` is labelled O(n) and its whole input is a single integer n;
its loop runs about n/12 times, and its own tests supply n up to 10^12. Neither
it nor the original Python finishes — `difftest.py` spent a 1800s budget on it
without completing one test, the only `error` in the loose tier's 100 rows.

It is left in place rather than moved, because moving it decides the
value-versus-size convention that `solutions-disputed/README.md` records as
open across eleven other rows. Until that is decided, this row is clean by
every gate that *can* run on it and untested by the one that cannot.

## Shape

    solutions/<problem_id>/<solution_id>.dfy

One method `Solve`, whose signature comes from the row's `dataclass_code` via
`signature.py`. The Python source is in the header comment, verbatim.
`data/call_depth.jsonl` records how deep each row's call chain runs — the
median row is two calls from `Solve`.
