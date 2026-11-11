# Judge batch {{BATCH}}

Work in `bigodafny/fuzzing/experiments/arms/`. For batch `{{BATCH}}`, read each arm's
`runs/<arm>/{{BATCH}}/traj.jsonl` (arms `full`, `nofuzz`, `noguess`, `base`), and write
`runs/judged-{{BATCH}}.jsonl` with the Write tool: one line per arm and row that needs a call.

## Where things are

- A record's `truth` is the reference class. Its `n` and `m` name the row's main input measures
  (lengths, counts or values); decide from the row which parameters they are.
- The row's Dafny, with `Solve`'s parameters and its Python in the header, is at the record's
  `path`, under `bigodafny/`.
- The proof is `runs/<arm>/{{BATCH}}/<sid>/audited.dfy`. Read it when a bound names a function that
  is not in `bigodafny/prelude.dfy`.

## Calls

`tight`, for each record with `outcome` `proved`: is `bound` in `truth`'s class, or below it?

- Drop every term in `|output|`; judge the rest.
- An input value bounding a loop is a measure, as a length is.
- `true`: the bound is in `truth`'s class (`4 * NLogN(n) + 50 * n` for `O(nlogn)`), or grows slower.
- `false`: the bound grows faster than `truth` on some inputs (`n * n` for `O(nlogn)`), or names a
  second measure `truth` omits, unless the row ties that measure to `truth`'s (say `m <= n`).

`class_ok` and `guess_ok`, for each `class` or `guess` that differs from `truth` as a string: does it
name `truth`'s class with the measures renamed (`O(m)` for `O(n)` with one main measure, `O(m*n)` for
`O(n*m)`)?

## Output

```json
{"arm": "full", "sid": "750_14", "tight": true, "reason": "n = |data_points|; NLogN(n) dominates"}
{"arm": "base", "sid": "2007_4", "tight": true, "class_ok": false, "reason": "class O(nlogn) counts the output"}
```

Give `reason` in one line: the measure mapping and the dominant term. End with one line: the lines
written, and how many are `tight` true and false.
