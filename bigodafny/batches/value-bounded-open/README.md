# `value-bounded-open/` — value-bounded rows with **no proof yet**

11 rows. Each one's real cost depends on how **large** an input is, while its
BigOBench label only counts how **many** inputs there are — and unlike the
22 in `solutions-proved/value-bounded/`, none has a verifying proof.

There are no `.dfy` files here, because there is nothing proved to hold.
`MANIFEST.jsonl` names each row, where it lives, the campaign that found it,
and the obstacle that stopped it. The rows themselves are untouched in their
status directories and still pass their behaviour gate; what is missing is a
complexity proof, not a translation. History: `../../CHANGELOG.md`.

## The rows

| row | label | what it would need |
|---|---|---|
| `1263_2538` | `O(n)` | a value-derived digit-count loop bound tied to a value parameter |
| `1306_126` | `O(n)` | the loop guard's inline sum hoisted into a ghost trace |
| `1332_16` | `O(nlogn)` | a log bound for the Fenwick-tree lowbit loop |
| `1364_161` | `O(logn)` | a triangular-number invariant plus `l <= log2(b)` via `Pow2` |
| `1626_179` | `O(nlogn)` | a halving-potential log lemma over a value-sized range |
| `1871_156` | `O(nlogn)` | its old proof repaired for Z3 5.1.0 (`../z3-upgrade/unresolved/`) |
| `1944_50` | `O(n)` | a doubling-search invariant over `Pow2` / `Log2` |
| `2358_103` | `O(nlogn)` | `floor(sqrt(v)) + 1` trips tied to a value parameter |
| `2465_212` | `O(nlogn)` | `Log2(0x40000000) = 30` in place of a brute `2^30` constant |
| `2819_926` | `O(n)` | `FloorDiv`, square-root and triangular-number bounds, four or five chained |
| `342_86` | `O(n)` | `floor(sqrt(v)) + 1` trips per element tied to a value parameter |

`1306_126`, `1871_156`, `1944_50` and `2819_926` have a reviewed obstacle; the
rest carry the campaign agent's `why_failed`.

## The failures do not transfer

Each row needs its own arithmetic. Unlike the `O(nlogn)` scaffold, written once
and reused, nothing here carries from one row to the next. The one row that
was blocked by something reusable, a prelude fact about sorted output
(`2423_48`), was proved once that fact was added.

## How a row leaves

- **Proved.** Its proof goes to `solutions-proved/value-bounded/` and its
  manifest entry moves with it.
- **Reviewer decides the convention does not apply.** The value is genuinely
  capped by the problem statement in a way that keeps the constant small.
  Record the cap and the reasoning.
- **Reviewer decides the label is wrong.** The row goes to
  `solutions-disputed/` if it is not there already.

Nothing leaves by relaxing the value-versus-size convention for one row.
