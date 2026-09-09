# Proving the complexity label

`solutions/` proves behaviour. `solutions-verified/` proves the label.

22 rows instrumented with a ghost step counter and a proved bound, plus 2 tight
copies in `solutions-nlogn/`. **24/24 verify, 0 contain `assume`, 24/24 emit
byte-identical Python to the row they were copied from.**

## Technique

```dafny
method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| + 2
```

The ghost out-parameter is erased at compile time. Convention in
`COMPLEXITY.md`; `proofs.py` re-verifies all of them and exits non-zero if any
proof contains `assume`.

## Results

| row | label | proved bound | verdict |
|---|---|---|---|
| `208_290` | O(1) | `6` | agrees |
| `945_255` | O(logn) | `4·Log2(n) + 8` | agrees |
| `5_100` | O(n) | `2n + 3` | agrees |
| `1011_368` | O(n) | `8n + 5` | agrees |
| `2742_57` | O(n) | `\|values\| + 6` | agrees |
| `459_199` | O(n+m) | `a + b + 2` | agrees |
| `1029_119` | O(n+m) | `2\|a\| + 2\|b\| + 3` | agrees |
| `685_777` | O(n+m) | `\|list1\| + \|list2\| + 8` | agrees |
| `1254_187` | O(n**2) | `n² + 12n + 70` | agrees |
| `827_148` | O(n**2) | `10000n² + 50000n + 600` | agrees* |
| `1855_50` | O(n**2) | `\|hour\| + \|minute\| + 12` | **label wrong** |
| `3046_65` | O(n*m) | `6n + 2·TotalLen + 3` | agrees |
| `3091_384` | O(n*m) | `4n + 3·TotalLen + 4` | agrees |
| `1138_83` | O(n*m) | `4n + 4` | **label wrong** |
| `1650_428` | O(n*m) | `4\|pairs\| + 10` | **label wrong** |
| `2719_94` | O(n*m) | `6\|values_list\| + 7` | **label wrong** |
| `2914_264` | O(n*m) | `7·max(n,0) + 3` | **label wrong** |
| `396_361` | O(n*m) | `8\|rectangles\| + 6` | **label wrong** |
| `525_273` | O(n*m) | `10n + 8` | **label wrong** |
| `187_193` | O(nlogn) | `2n(CeilLog2(n)+1) + 6` | agrees |
| `603_284` | O(nlogn) | `2n² + 2n + 4` | not established here |
| `1484_82` | O(nlogn) | `2n² + 2n + 2·SumLen + 6` | not established here |

`solutions-nlogn/` carries the tight bound for the last two:
`2n(CeilLog2(n)+1) + …`, which does establish O(n log n) for both.

## O(n*m): the label is right when the body scans a row, wrong when it does not

Eight rows examined, **six wrong, two right**, and the split is not subtle.

`3046_65` and `3091_384` walk every token of every row, so a wider row really
does cost more and the bound carries a genuine second dimension. The six wrong
ones read a **fixed number of positions per row** — `row[0]`, `row[1]`,
sometimes up to `row[4]` — and never scan one. A row of width 1000 costs them
exactly what a row of width 2 costs. There is no second dimension to name, so
the honest bound is O(n).

That is a usable rule for the remaining 40 rows carrying this label: read the
loop body, not the input shape. Six of eight is a rate, not yet a prior for the
rest — the sample was drawn shortest-file-first, and short bodies are exactly
the ones that do not scan.

`1138_83` fails differently again: its `m` is a scalar modulus, a number the
program divides by, not a size at all.

## `1855_50`: an O(n**2) label on straight-line code

The first label proved wrong outside the O(n*m) family. The row has no loop and
no recursion over a collection — it parses two numbers, does six arithmetic
operations and prints. The only input-dependent work is the two `ParseInt`
calls, one recursion level per character. Nothing in it can exhibit any growth
rate, let alone a quadratic one.

The O(n*m) failures name a dimension that does not vary; this one names a
growth rate no part of the code has. Both are what fitting a curve to profiling
runs does to a program with nothing to profile.

## Logarithms: match the log's rounding to the code's rounding

`945_255` is the first logarithmic bound proved for a row that does not sort,
and it wants the **opposite** log from the merge-sort rows.

    merge sort recurses on ceil(k/2)  ->  CeilLog2, ceiling
    a loop doing m := m / 2 rounds down  ->  Log2, floor

With the matching one, the key step holds by definition — `m >= 2 ==>
Log2(m/2) == Log2(m) - 1` — and the invariant closes with no lemma at all.
With the other, it is false at some small k and the induction cannot close.
The rule generalises the `solutions-nlogn/` finding: it was never "use a
ceiling log", it was "match the code".

`187_193` is the first row to get the tight n log n bound on the first pass,
by reusing that recursion-tree argument. `603_284` and `1484_82` each needed a
quadratic fallback and a second copy; the machinery is now cheap to reuse.

## Two measurements that changed the charging convention

Both in Dafny 4.11.0's Python backend, both in `COMPLEXITY.md`.

**Sequence append is lazy.** `s := s + [x]` builds a deferred concat node.
Append-only accumulation is linear (n=64k in 0.149s); reading `s[i]` between
appends forces a flatten every time and is quadratic (n=64k in 7.876s). Taking
`|s|` is free. The old table charged `|s|` unconditionally — sound, but it made
every accumulate-then-emit row look quadratic and put its label out of reach.

**`Join` is superlinear**, about L^1.2 — above linear, below quadratic. So
`SumLen(parts) + |parts|` *undercharges* it, and undercharging is the one error
that voids a proof. Rows whose output is one line per input item are therefore
deferred, not attempted: `171_82`, `89_463`, `2602_57` and `378_20` are each
provable except for this term. Every proof so far prints a single value.

## The gates were checking the wrong file

`validate.py` and `difftest.py` both resolve a row by scanning
`SOLUTIONS, INEXACT, UNVERIFIED, VERIFIED` and returning the **first** hit. A
proved row exists in two places at once, and `solutions/` is scanned first — so
every "still passes its tests" claim for `solutions-verified/` was measured on
the uninstrumented original. This is the third instance of one bug:
`precheck.py` had it, was fixed with `find_all()`, and the fix never reached
the other two gates.

Neither gate was edited here — an agent may not edit a gate it is judged by.
Instead:

- `validate.py --solutions-dir solutions-verified` points the existing flag at
  the instrumented copies: **20/22 valid**, and the 2 failures are `1855_50`
  and `2742_57`, both `loose` rows where a byte-diff against the stored output
  is the wrong question. Their own Python scores 0.477 and 0.0 on the same
  comparison.
- `difftest.py` has no such flag, so equivalence was established more strongly
  instead: the emitted Python of all 12 new proofs is **byte-identical** to
  that of the row they were copied from, with zero occurrences of `steps`.
  Identical compiled code cannot differ on any input, which is a stronger
  statement than re-running a sample of tests.

A second hazard found the same way: `validate.py --only <ids>` **overwrites**
the corpus-wide `data/validation.jsonl` with just those rows, and `dataset.py`
then reports 4 valid translations instead of 529. Restored from git. Use
`--out-prefix` for partial runs; it redirects the output file.

## Preconditions were checked, not assumed

`precheck.py` over all 12 new proofs: 16 clauses, **16 ok, 0 violated, 0
unchecked, 0 no-data**. No new precondition was introduced by any of them —
each carries exactly what its `solutions/` original already carried.

`2914_264` states its bound as `7 · max(n, 0) + 3` rather than adding
`requires n >= 1`. The row answers a non-positive n perfectly well, so a
precondition would have excluded inputs it handles — the mistake `1254_187`
carried undetected for two waves.
