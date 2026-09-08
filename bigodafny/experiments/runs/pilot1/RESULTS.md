# Complexity-proving experiment

22 runs: 10 labeled, 12 blind.

## Proof rate

| arm | attempted | proved | verified but gate-failed | no bound |
|---|---|---|---|---|
| labeled | 10 | 7 | 2 | 2 |
| blind | 12 | 6 | 6 | 5 |

## Blind arm: did it name the class

- guessed on 12 of 12 examples (0 excluded for a leak attempt)
- correct: **6/12** = 50%

| true class | guessed right | n |
|---|---|---|
| `O(n)` | 0 | 2 |
| `O(n+m)` | 1 | 1 |
| `O(nlogn)` | 2 | 3 |
| `O(n*m)` | 2 | 2 |
| `O(n**2)` | 1 | 2 |
| `O(nlogn+mlogm)` | 0 | 1 |
| `O(n**2+m**2)` | 0 | 1 |

### Confusion (rows = true, cols = guessed)

| true \ guess | `O(1)` | `O(n)` | `O(n+m)` | `O(nlogn)` | `O(n*m)` | `O(n**2)` | `O(n**2+m**2)` |
|---|---|---|---|---|---|---|---|
| `O(n)` | 1 |  |  | 1 |  |  |  |
| `O(n+m)` |  |  | 1 |  |  |  |  |
| `O(nlogn)` |  |  |  | 2 |  | 1 |  |
| `O(n*m)` |  |  |  |  | 2 |  |  |
| `O(n**2)` |  |  |  |  |  | 1 | 1 |
| `O(nlogn+mlogm)` |  | 1 |  |  |  |  |  |
| `O(n**2+m**2)` |  |  |  |  |  | 1 |  |

## Where a passing proof disagrees with the label

A proof gives an UPPER bound, so the direction of a disagreement decides
what it means. Only a bound strictly tighter than the label contradicts
it -- an n log n program also satisfies steps <= c*n^2, so a looser bound
is consistent with the label and carries no news. An agent charging a seq
append flatly produces exactly that kind of loose bound.

**1 bound(s) excluded as degenerate**: a constant bound on a
program that loops over its input, bought by folding the statement's
numeric cap into the constant. True, verifiable, and vacuous.

- blind `2381_176` (label `O(n)`): `20000000000`

### tighter: 2 -- **refutes the label** -- provably cheaper than claimed

| arm | sid | label | proved | drift | ensures |
|---|---|---|---|---|---|
| blind | `1243_0` | `O(nlogn+mlogm)` | `O(n+m)` | sort-mismatch | `10 * |s1| + 10 * |s2| + 30` |
| labeled | `1243_0` | `O(nlogn+mlogm)` | `O(n+m)` | sort-mismatch | `2 * |s1| + 2 * |s2| + 3` |

### same-rank: 2 -- same growth rank, different naming of the sizes

| arm | sid | label | proved | drift | ensures |
|---|---|---|---|---|---|
| blind | `1718_1166` | `O(n*m)` | `O(n**2+m**2)` | - | `20 * N1 * N1 + 20 * N2 * N2 + 20 * N1 * N2 + 20 * N1 + 20 * N2 + 30` |
| labeled | `1718_1166` | `O(n*m)` | `O(n**2+m**2)` | - | `2 * N1 * N1 + 2 * N2 * N2 + 4 * N1 + 2 * N2 + 4` |

### looser: 4 -- consistent with the label; the proof is loose, not news

| arm | sid | label | proved | drift | ensures |
|---|---|---|---|---|---|
| blind | `2650_140` | `O(nlogn)` | `O(n**2)` | append-in-loop | `50 * n * n + 50 * n + 50` |
| blind | `354_95` | `O(n)` | `O(nlogn)` | - | `a * (2 * CeilLog2(a) + 5) + 10` |
| labeled | `1563_497` | `O(nlogn)` | `O(n**2)` | - | `|values| * |values| + |values| + 10` |
| labeled | `2650_140` | `O(nlogn)` | `O(n**2)` | append-in-loop | `4 * n * n + 15 * n + 16` |

## Gate failures

| gate | labeled | blind |
|---|---|---|
| did not verify | 1 | 0 |
| used `assume` | 0 | 0 |
| compiled control flow changed | 0 | 1 |
| behaviour changed | 0 | 0 |
| a `requires` excludes real inputs | 0 | 0 |

## Difficulty: declared before the run vs measured

| difficulty_static | n | proved | mean dafny calls | mean difficulty_measured |
|---|---|---|---|---|
| 1 | 2 | 2 | 1.5 | 1.0 |
| 2 | 11 | 6 | 2.8 | 2.0 |
| 3 | 5 | 3 | 2.8 | 2.0 |
| 4 | 4 | 2 | 6.5 | 2.8 |

## Anti-cheat

- blind examples with a leak attempt: **0**

