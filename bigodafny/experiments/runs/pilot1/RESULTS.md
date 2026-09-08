# Complexity-proving experiment

8 runs: 4 labeled, 4 blind.

## Proof rate

| arm | attempted | proved | verified but gate-failed | no bound |
|---|---|---|---|---|
| labeled | 4 | 4 | 0 | 0 |
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

Split by whether the TRANSLATION drifts from its Python. A proof is
about the Dafny; where the two differ in shape, a disagreement with the
label is a fact about this dataset's translation, not about BigOBench.

- disagreements on rows with NO drift signal: **2**
- disagreements on rows WITH a drift signal:  **4**

| arm | sid | label | proved | drift | ensures |
|---|---|---|---|---|---|
| blind | `1243_0` | `O(nlogn+mlogm)` | `O(n+m)` | sort-mismatch | `10 * |s1| + 10 * |s2| + 30` |
| blind | `1718_1166` | `O(n*m)` | `O(n**2+m**2)` | - | `20 * N1 * N1 + 20 * N2 * N2 + 20 * N1 * N2 + 20 * N1 + 20 * N2 + 30` |
| blind | `2650_140` | `O(nlogn)` | `O(n**2)` | append-in-loop | `50 * n * n + 50 * n + 50` |
| labeled | `1243_0` | `O(nlogn+mlogm)` | `O(n+m)` | sort-mismatch | `2 * |s1| + 2 * |s2| + 3` |
| labeled | `1718_1166` | `O(n*m)` | `O(n**2+m**2)` | - | `2 * N1 * N1 + 2 * N2 * N2 + 4 * N1 + 2 * N2 + 4` |
| labeled | `2650_140` | `O(nlogn)` | `O(n**2)` | append-in-loop | `4 * n * n + 15 * n + 16` |

## Gate failures

| gate | labeled | blind |
|---|---|---|
| did not verify | 0 | 0 |
| used `assume` | 0 | 0 |
| compiled control flow changed | 0 | 0 |
| behaviour changed | 0 | 0 |
| a `requires` excludes real inputs | 0 | 0 |

## Difficulty: declared before the run vs measured

| difficulty_static | n | proved | mean dafny calls | mean difficulty_measured |
|---|---|---|---|---|
| 1 | 2 | 2 | 1.5 | 1.0 |
| 2 | 2 | 2 | 2.0 | 1.0 |
| 3 | 2 | 2 | 5.0 | 2.5 |
| 4 | 2 | 2 | 13.0 | 3.5 |

## Anti-cheat

- blind examples with a leak attempt: **0**

