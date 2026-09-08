# Complexity-proving experiment

6 runs: 2 labeled, 4 blind.

## Proof rate

| arm | attempted | proved | verified but gate-failed | no bound |
|---|---|---|---|---|
| labeled | 2 | 2 | 0 | 0 |
| blind | 4 | 4 | 0 | 0 |

## Blind arm: did it name the class

- guessed on 4 of 4 examples (0 excluded for a leak attempt)
- correct: **1/4** = 25%

| true class | guessed right | n |
|---|---|---|
| `O(nlogn)` | 0 | 1 |
| `O(n*m)` | 1 | 1 |
| `O(nlogn+mlogm)` | 0 | 1 |
| `O(n**2+m**2)` | 0 | 1 |

### Confusion (rows = true, cols = guessed)

| true \ guess | `O(n)` | `O(n*m)` | `O(n**2)` |
|---|---|---|---|
| `O(nlogn)` |  |  | 1 |
| `O(n*m)` |  | 1 |  |
| `O(nlogn+mlogm)` | 1 |  |  |
| `O(n**2+m**2)` |  |  | 1 |

## Where a passing proof disagrees with the label

| arm | sid | label | proved | ensures |
|---|---|---|---|---|
| blind | `1243_0` | `O(nlogn+mlogm)` | `O(n+m)` | `10 * |s1| + 10 * |s2| + 30` |
| blind | `1718_1166` | `O(n*m)` | `O(n**2+m**2)` | `20 * N1 * N1 + 20 * N2 * N2 + 20 * N1 * N2 + 20 * N1 + 20 * N2 + 30` |
| blind | `2650_140` | `O(nlogn)` | `O(n**2)` | `50 * n * n + 50 * n + 50` |
| labeled | `1243_0` | `O(nlogn+mlogm)` | `O(n+m)` | `2 * |s1| + 2 * |s2| + 3` |

## Gate failures

| gate | labeled | blind |
|---|---|---|
| did not verify | 0 | 0 |
| used `assume` | 0 | 0 |
| compiled control flow changed | 0 | 0 |
| behaviour changed | 0 | 0 |

## Difficulty: declared before the run vs measured

| difficulty_static | n | proved | mean dafny calls | mean difficulty_measured |
|---|---|---|---|---|
| 1 | 2 | 2 | 1.5 | 1.0 |
| 2 | 2 | 2 | 2.0 | 1.0 |
| 3 | 1 | 1 | 4.0 | 2.0 |
| 4 | 1 | 1 | 6.0 | 3.0 |

## Anti-cheat

- blind examples with a leak attempt: **0**

