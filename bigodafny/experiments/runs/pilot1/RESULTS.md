# Complexity-proving experiment

36 runs: 19 labeled, 17 blind.

## Proof rate

| arm | attempted | proved | verified but gate-failed | no bound |
|---|---|---|---|---|
| labeled | 19 | 13 | 4 | 3 |
| blind | 17 | 10 | 5 | 4 |

## Blind arm: did it name the class

- guessed on 17 of 17 examples (0 excluded for a leak attempt)
- correct: **7/17** = 41%

| true class | guessed right | n |
|---|---|---|
| `O(n)` | 0 | 3 |
| `O(n+m)` | 1 | 1 |
| `O(nlogn)` | 2 | 5 |
| `O(n*m)` | 2 | 3 |
| `O(n**2)` | 2 | 3 |
| `O(nlogn+mlogm)` | 0 | 1 |
| `O(n**2+m**2)` | 0 | 1 |

### Confusion (rows = true, cols = guessed)

| true \ guess | `O(1)` | `O(n)` | `O(n+m)` | `O(nlogn)` | `O(n*m)` | `O(n**2)` | `O(n**2+m**2)` |
|---|---|---|---|---|---|---|---|
| `O(n)` | 1 |  |  | 1 |  | 1 |  |
| `O(n+m)` |  |  | 1 |  |  |  |  |
| `O(nlogn)` |  |  |  | 2 |  | 3 |  |
| `O(n*m)` |  |  |  |  | 2 | 1 |  |
| `O(n**2)` |  |  |  |  |  | 2 | 1 |
| `O(nlogn+mlogm)` |  | 1 |  |  |  |  |  |
| `O(n**2+m**2)` |  |  |  |  |  | 1 |  |

### Do the wrong guesses lean one way?

- overestimated (guessed a slower class): 5
- underestimated: 2
- wrong but same growth rank: 3
- one-sided sign test on the 7 directional errors: p = 0.227

At this sample size that is not evidence of a lean, whatever the
matrix looks like. Recorded so the question can be re-asked when
the run is larger.

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

### tighter: 3 -- **refutes the label** -- provably cheaper than claimed

| arm | sid | label | proved | drift | ensures |
|---|---|---|---|---|---|
| blind | `1243_0` | `O(nlogn+mlogm)` | `O(n+m)` | sort-mismatch | `10 * |s1| + 10 * |s2| + 30` |
| labeled | `1243_0` | `O(nlogn+mlogm)` | `O(n+m)` | sort-mismatch | `2 * |s1| + 2 * |s2| + 3` |
| labeled | `2281_358` | `O(n+mlogm)` | `O(n)` | sort-mismatch | `3 * n + 3` |

### same-rank: 4 -- same growth rank, different naming of the sizes

| arm | sid | label | proved | drift | ensures |
|---|---|---|---|---|---|
| blind | `1718_1166` | `O(n*m)` | `O(n**2+m**2)` | - | `20 * N1 * N1 + 20 * N2 * N2 + 20 * N1 * N2 + 20 * N1 + 20 * N2 + 30` |
| blind | `1827_44` | `O(n**2)` | `O(n**2+m**2)` | append-in-loop | `BIG * (XCAP + 2) + BIG * (XCAP + 2) + (a + BIG) * a + BIG * (a + 1)` |
| labeled | `1718_1166` | `O(n*m)` | `O(n**2+m**2)` | - | `2 * N1 * N1 + 2 * N2 * N2 + 4 * N1 + 2 * N2 + 4` |
| labeled | `378_20` | `O(n*m)` | `O(n**2)` | append-in-loop | `|pairs| * |pairs| + 20 * |pairs| + 20` |

### looser: 5 -- consistent with the label; the proof is loose, not news

| arm | sid | label | proved | drift | ensures |
|---|---|---|---|---|---|
| blind | `1915_158` | `O(n+m)` | `O(n*m)` | - | `A * n + 2 * A * m + 2 * A + 20` |
| blind | `2650_140` | `O(nlogn)` | `O(n**2)` | append-in-loop | `50 * n * n + 50 * n + 50` |
| blind | `354_95` | `O(n)` | `O(nlogn)` | - | `a * (2 * CeilLog2(a) + 5) + 10` |
| labeled | `1563_497` | `O(nlogn)` | `O(n**2)` | - | `|values| * |values| + |values| + 10` |
| labeled | `2650_140` | `O(nlogn)` | `O(n**2)` | append-in-loop | `4 * n * n + 15 * n + 16` |

## Gate failures

| gate | labeled | blind |
|---|---|---|
| did not verify | 2 | 2 |
| used `assume` | 0 | 0 |
| compiled control flow changed | 2 | 1 |
| behaviour changed | 1 | 0 |
| a `requires` excludes real inputs | 0 | 0 |

## Difficulty: declared before the run vs measured

| difficulty_static | n | proved | mean dafny calls | mean difficulty_measured |
|---|---|---|---|---|
| 1 | 3 | 2 | 1.5 | 1.3 |
| 2 | 16 | 12 | 2.1 | 1.6 |
| 3 | 9 | 6 | 2.7 | 1.9 |
| 4 | 8 | 3 | 5.0 | 2.6 |

## Anti-cheat

- blind examples with a leak attempt: **0**

