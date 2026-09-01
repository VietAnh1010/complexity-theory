# Proving the complexity label

`solutions/` proves behaviour. `solutions-verified/` proves the label.

10 rows instrumented with a ghost step counter and a proved bound.
**10/10 verify, 0 contain `assume`, 10/10 still pass their tests.**

## Technique

```dafny
method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| + 2
```

The ghost out-parameter is erased at compile time — the emitted Python is
`def Solve(n, a__list)` with zero occurrences of `steps`. One file both runs
under the harness and carries a machine-checked proof. Convention in
`COMPLEXITY.md`; `proofs.py` re-verifies all of them and exits non-zero if any
proof contains `assume`.

## Results

| row | label | proved bound | verdict |
|---|---|---|---|
| `459_199` | O(n+m) | `a + b + 2` | agrees |
| `1029_119` | O(n+m) | `2\|a\| + 2\|b\| + 3` | agrees |
| `1254_187` | O(n**2) | `(n+2)^2 + 8(n+2) + 20` | agrees |
| `827_148` | O(n**2) | `10000n^2 + 50000n + 600` | agrees* |
| `5_100` | O(n) | `2n + 3` | agrees |
| `1011_368` | O(n) | `8n + 5` | agrees |
| `1138_83` | O(n*m) | `4n + 4` | **label wrong** |
| `1650_428` | O(n*m) | `4\|pairs\| + 10` | **label wrong** |
| `603_284` | O(nlogn) | `2n^2 + 2n + 4` | **not established** |
| `1484_82` | O(nlogn) | `2n^2 + 2n + 2·SumLen + 6` | **not established** |

## Both O(n*m) labels are wrong

Same cause twice: the label's `m` names nothing that varies. In `1138_83` it is
a scalar modulus; in `1650_428` every row is exactly two tokens. True cost is
O(n) in both. 48 rows carry this label dataset-wide; two of two examined are
wrong, which is a reason for suspicion, not yet a rate.

## O(n log n) was not reached

Dafny has no `log`. Both sort rows fall back to an honest `O(n^2)` via an opaque
`SortCost(n) <= 2n^2 + 1`, proved rather than assumed. Reaching `n log n` needs
a `Log2` recursion-tree argument with floor/ceil asymmetry. The weaker bound is
true and strictly weaker than the label — reported, not massaged.

`1484_82` is weaker in a second dimension: its trailing comparison loop is
bounded by total string length, not by `n`, so it is charged against
`SumLen(numbers)`.

## `827_148` has no complexity without a value cap

Its inner catch-up loop iterates a data-dependent number of times. No
polynomial-in-n bound exists until values are bounded, so the proof takes the
problem's stated `1 <= d_i <= 1000` as a precondition and folds the cap into the
constant. The label assumes the same thing silently.

## Preconditions were checked, not assumed

A too-strong precondition makes a proof true and empty. Every added `requires`
was evaluated against every stored input:

- 8 of 10 rows: holds on all tiers.
- `827_148`: all 35 public+private hold; 39 of 98 generated violate.
- `1254_187`: all 2 public+private hold; 48 of 100 generated violate.

Every violation is in the generated tier and breaks the problem's own stated
constraints — `827_148` receives a `0` where the statement requires `>= 1`,
`1254_187` receives `n = 0` where it requires `n >= 1`. So the proofs cover
every input the validator gates on, and separately: **BigOBench's generated
tests range outside the constraints their own problem statements declare.**

## Verification found a latent defect

`459_199`'s original `decreases if n+m>=0 then n+m else 0` does not decrease on
the terminal branch, so that file never verified — before any instrumentation.
It had passed tests since wave 4. Two sort rows likewise indexed `l[i+1]`
without a length fact. Tests never noticed any of it.
