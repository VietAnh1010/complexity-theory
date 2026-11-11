# Judge bounds and classes against the reference class

You judge batch `{{BATCH}}`. Read `{{DIR}}/input.jsonl`, and write `{{DIR}}/output.jsonl` with one
line per input line. Do not open `key.jsonl`, or anything else under `fuzzing/experiments/arms/runs/`:
which agent wrote an item is hidden from you on purpose.

## Input

```json
{"item": "1-007", "kind": "bound", "sid": "750_14", "row": "solutions/750/750_14.dfy",
 "truth": "O(nlogn)", "value": "4 * NLogN(|data_points|) + 50 * |data_points| + 20 + |output|"}
```

- `row`, under `bigodafny/`, is the row's Dafny: `Solve`'s parameters, and the Python it was translated
  from in its header. Read it to know what each parameter is.
- `truth` is the reference class. Its `n` and `m` name the row's main input measures (lengths, counts
  or values); decide from the row which parameters they are.
- `value` is a proved bound on `steps` (`kind: bound`) or a stated class (`kind: class`).
- `bigodafny/prelude.dfy` defines the functions a bound may call (`NLogN`, `CeilLog2`, `SumLen`, ...).

## Rules

`kind: bound`: give `relation`, the bound's class against `truth`.

- Drop every term in `|output|`; judge the rest.
- An input value bounding a loop is a measure, as a length is.
- `equal`: the bound is in `truth`'s class (`4 * NLogN(n) + 50 * n` for `O(nlogn)`).
- `looser`: the bound grows faster than `truth` on some inputs (`n * n` for `O(nlogn)`).
- `tighter`: the bound grows slower than `truth` (`n` for `O(nlogn)`).
- A bound over a second measure `truth` omits is `looser`, unless the row ties that measure to `truth`'s
  (say the Python asserts `m <= n`).

`kind: class`: give `same`, true if `value` names `truth`'s class with the measures renamed
(`O(m)` for `O(n)` when the row has one main measure, `O(m*n)` for `O(n*m)`), else false.

## Output

```json
{"item": "1-007", "relation": "equal", "reason": "NLogN(|data_points|) dominates; n = |data_points|"}
{"item": "1-012", "same": true, "reason": "m is the only measure, |s|"}
```

`reason` is one line: the measure mapping and the dominant term. Write the file with the Write tool.
End with one line: the item count, and the counts per relation and per `same`.
