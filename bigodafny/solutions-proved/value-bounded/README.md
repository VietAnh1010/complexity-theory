# `value-bounded/`: the label counts items, the code depends on their magnitude

Proved rows whose cost depends on **how large** an input is, while the
label counts only **how many** inputs there are. Unproved rows of this kind are
in `batches/value-bounded-open/`.

Example, `1948_388`: the Python computes `sqrt(8*k+1)` from one input, so its
label is `O(1)`. Dafny has no float `sqrt`, so the translation searches
`while s*s < target`, about `sqrt(k)` steps: 28 for `k = 100`, a billion for
`k = 10**18`.

BigOBench timed its labels, which treats a capped value as constant;
`COMPLEXITY.md` counts the value as a size (`relation: looser-structural`). The two disagree here by design.

These are copies like the rest of `solutions-proved/`. The rows themselves
are all in `solutions-disputed/`. `MANIFEST.jsonl` gives each row's bound, path and
reason.

| row | label | found by |
|---|---|---|
| `1043_358` | `O(n)` | prove-sample-7 |
| `1386_19` | `O(nlogn)` | prove-sample-2, prove-sample-5 |
| `1386_38` | `O(n)` | prove-sample-2 |
| `1484_26` | `O(n)` | prove-sample |
| `1580_12` | `O(n+m)` | prove-sample-6 |
| `1678_68` | `O(1)` | prove-sample-7 rerun |
| `1820_180` | `O(n)` | prove-sample-4 |
| `1867_16` | `O(n)` | prove-sample-3 |
| `1871_291` | `O(n)` | prove-sample |
| `1915_158` | `O(n+m)` | prove-sample |
| `1948_388` | `O(1)` | prove-sample-4 (failed), prove-sample-6 (proved) |
| `2128_34` | `O(n**2)` | prove-sample |
| `2254_6` | `O(n)` | prove-sample |
| `2358_421` | `O(n)` | prove-sample-4 |
| `2423_48` | `O(nlogn)` | prove-sample-3, prove-sample-4 (failed both; proved by hand) |
| `2607_90` | `O(n)` | prove-sample |
| `305_76` | `O(nlogn+mlogm)` | prove-sample-3 |
| `704_351` | `O(1)` | prove-sample-3 |
| `794_794` | `O(n)` | prove-sample-7 |
| `810_131` | `O(n)` | prove-sample |
| `2942_55` | `O(n)` | main agent, re-translation |
| `305_284` | `O(n+m)` | main agent, re-translation |

## Causes

- **A loop over a value:** `1580_12` loops until `b*i` reaches `a*c`;
  `794_794` loops to a per-test value; `305_284` searches `range(p, q)`.
- **Output whose length is a value:** `1043_358` prints `"3" * (v - 1)`;
  `2254_6` prints a string of length `n_i`.
- **Euclid's depth:** `1386_19`, `1386_38`, `1871_291`, `1915_158`, `1678_68`
  charge `Gcd` its depth, a log of the values. A running gcd only shrinks, so
  its depths telescope to `O(n + log max)`, still a value: `1915_158` proves
  this (`GcdTelescopeFirst`); `1386_38` charges every gcd its full depth, a
  looser `O(n log max)`. `2942_55` computes
  `2**m` by squaring, costing each exponent's bit length (`TokBits`).

Unlike sorting, where one prelude lemma serves every row, each value-bounded
proof needs its own arithmetic; nothing carries over
(`batches/value-bounded-open/` lists what each open row needs).

## Getting in

- `relation: looser-structural` in a campaign's `label_relation.jsonl`, with a
  reason naming an input **value**: move the proof file here.
- `obstacle: value-to-size` with no proof: the row goes to
  `batches/value-bounded-open/MANIFEST.jsonl` instead.

Name the campaign that found it.

## Getting out

1. **The label is wrong:** correct the label in the dataset.
2. **The cap is real and small:** record it and the reasoning.
3. **A tighter bound without the value exists:** prove it.
4. **The proof stops verifying:** move it to `batches/value-bounded-open/`.

Never exempt one row from the rule that an input value is a size.
