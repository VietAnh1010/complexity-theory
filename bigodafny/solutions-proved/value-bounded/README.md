# `value-bounded/`: the label counts items, the code depends on their magnitude

Proved rows whose cost depends on **how large** an input is, while the
label counts only **how many** inputs there are. An unproved row of this kind stays open with
obstacle `value-to-size` in its campaign trajectory.

Example, `1948_388`: the Python computes `sqrt(8*k+1)` from one input, so its
label is `O(1)`. Dafny has no float `sqrt`, so the translation searches
`while s*s < target`, about `sqrt(k)` steps: 28 for `k = 100`, a billion for
`k = 10**18`.

BigOBench timed its labels, which treats a capped value as constant;
`COMPLEXITY.md` counts the value as a size (`relation: looser-structural`). The two disagree here by design.

These are copies like the rest of `solutions-proved/`. The rows themselves stay in
their status directories. `MANIFEST.jsonl` gives each row's label, bound, path, the campaign
that found it, and the reason.

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
proof needs its own arithmetic; nothing carries over.

## Getting in

- `relation: looser-structural` in a campaign's `label_relation.jsonl`, with a
  reason naming an input **value**: move the proof file here.
- No proof, and `why_failed` says the cost depends on an input **value**: record obstacle
  `value-to-size`; nothing moves.

Name the campaign that found it.

## Getting out

1. **The label is wrong:** correct the label in the dataset.
2. **The cap is real and small:** record it and the reasoning.
3. **A tighter bound without the value exists:** prove it.
4. **The proof stops verifying:** remove it; the row is open again.

Never exempt one row from the rule that an input value is a size.
