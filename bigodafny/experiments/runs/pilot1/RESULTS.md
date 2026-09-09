# Complexity-proving experiment

43 runs scored: 21 labeled, 18 blind.

4 further example(s) hold only a `gave_up` stub with an
untouched file -- an agent cut off by a rate limit, or still running.
Not a give-up, and not counted in any rate below: blind/`1047_641`, blind/`2465_212`, labeled/`1332_16`, labeled/`2269_21`

## Proof rate

| arm | attempted | proved | verified but gate-failed | no bound |
|---|---|---|---|---|
| labeled | 21 | 16 | 3 | 3 |
| blind | 18 | 13 | 3 | 3 |

## Blind arm: did it name the class

- guessed on 20 of 20 blind examples (0 excluded for a leak attempt); 2 of these come from an agent cut off before it could finish the proof, whose guess is still valid
- correct: **7/20** = 35%
- on rows the translation cannot have re-classed: **5/13** = 38%
- on rows containing a class-changing construct: **2/7** = 29%

The blind agent reads the **Dafny**; the label was measured on the **Python**. A seq functional update in a loop is O(1) in CPython and a full copy in Dafny, and a `set` built in a loop is quadratic in Dafny -- both measured. On a row containing one, the two programs can sit in different classes, and an agent that reads its input correctly is then scored wrong against the label.

`1039_15` is the established case, not a hypothesis: the blind agent guessed `O(n**2)` before proving, PROVED `O(n**2)`, and wrote that the Python is O(n log n) because array assignment is O(1) there. It is scored incorrect against an `O(nlogn)` label. Its labeled twin reached the same quadratic independently.

The split above is reported, not corrected: the pooled number is still the honest answer to "did it name the label". It is the wrong denominator for "can it read a program".

| sid | label | guess | scored |
|---|---|---|---|
| `1039_15` | `O(nlogn)` | `O(n**2)` | incorrect |
| `1180_626` | `O(n+m)log(n+m)` | `O(n+mlogm)` | incorrect |
| `1332_16` | `O(nlogn)` | `O(n**2)` | incorrect |
| `1718_1166` | `O(n*m)` | `O(n*m)` | correct |
| `2465_212` | `O(nlogn)` | `O(nlogn)` | correct |
| `2650_140` | `O(nlogn)` | `O(n**2)` | incorrect |
| `378_20` | `O(n*m)` | `O(n**2)` | incorrect |

| true class | guessed right | n |
|---|---|---|
| `O(n)` | 0 | 3 |
| `O(n+m)` | 1 | 1 |
| `O(nlogn)` | 2 | 6 |
| `O(n*m)` | 2 | 3 |
| `O(n**2)` | 2 | 4 |
| `O(nlogn+mlogm)` | 0 | 1 |
| `O(n+m)log(n+m)` | 0 | 1 |
| `O(n**2+m**2)` | 0 | 1 |

### Confusion (rows = true, cols = guessed)

| true \ guess | `O(1)` | `O(n)` | `O(n+m)` | `O(nlogn)` | `O(n*m)` | `O(n**2)` | `O(n+mlogm)` | `O(n**2+m**2)` |
|---|---|---|---|---|---|---|---|---|
| `O(n)` | 1 |  |  | 1 |  | 1 |  |  |
| `O(n+m)` |  |  | 1 |  |  |  |  |  |
| `O(nlogn)` |  |  |  | 2 |  | 4 |  |  |
| `O(n*m)` |  |  |  |  | 2 | 1 |  |  |
| `O(n**2)` |  | 1 |  |  |  | 2 |  | 1 |
| `O(nlogn+mlogm)` |  | 1 |  |  |  |  |  |  |
| `O(n+m)log(n+m)` |  |  |  |  |  |  | 1 |  |
| `O(n**2+m**2)` |  |  |  |  |  | 1 |  |  |

### Do the wrong guesses lean one way?

- overestimated (guessed a slower class): 6
- underestimated: 3
- wrong but same growth rank: 4
- one-sided sign test on the 9 directional errors: p = 0.254

At this sample size that is not evidence of a lean, whatever the
matrix looks like. Recorded so the question can be re-asked when
the run is larger.

## Claimed refutations, and which of them the proof carries

A ghost step counter proves an UPPER bound. It can refute a label only
by proving something strictly TIGHTER -- the program is faster than
claimed. It can never show a program is SLOWER than claimed: that needs
a lower bound, and this method cannot produce one. An agent that charges
a string concat honestly, lands on n^2 against an O(n) label, and writes
`refutes` has proved a bound the label already satisfies.

The agent's own verdict is recorded as its belief. The direction of the
bound decides what was established.

- claimed `refutes`, proof is tighter -- **established**: 2
  - labeled `1243_0` `O(nlogn+mlogm)` -> `O(n+m)`
  - labeled `2281_358` `O(n+mlogm)` -> `O(n)`
- claimed `refutes`, proof is only an upper bound -- **not established**: 6
  - blind `1718_1166` `O(n*m)` -> `O(n**2+m**2)` (same-rank)
  - labeled `1563_497` `O(nlogn)` -> `O(n**2)` (looser)
  - labeled `1718_1166` `O(n*m)` -> `O(n**2+m**2)` (same-rank)
  - labeled `2650_140` `O(nlogn)` -> `O(n**2)` (looser)
  - labeled `378_20` `O(n*m)` -> `O(n**2)` (same-rank)
  - labeled `794_794` `O(n)` -> `O(n**2)` (looser)

The mechanism those agents describe -- a string or seq concat inside a
loop, genuinely linear in Dafny where CPython amortises it away -- may
well be right. It is not what their artifact proves.

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
| blind | `1827_44` | `O(n**2)` | `O(n**2+m**2)` | - | `BIG * (XCAP + 2) + BIG * (XCAP + 2) + (a + BIG) * a + BIG * (a + 1)` |
| labeled | `1718_1166` | `O(n*m)` | `O(n**2+m**2)` | - | `2 * N1 * N1 + 2 * N2 * N2 + 4 * N1 + 2 * N2 + 4` |
| labeled | `378_20` | `O(n*m)` | `O(n**2)` | - | `|pairs| * |pairs| + 20 * |pairs| + 20` |

### looser: 9 -- consistent with the label; the proof is loose, not news

| arm | sid | label | proved | drift | ensures |
|---|---|---|---|---|---|
| blind | `1039_15` | `O(nlogn)` | `O(n**2)` | - | `10 * (ParseInt(n_str)) * (ParseInt(n_str)) + 100 * (ParseInt(n_str)) + |a_list_str| + |n_str| + 100` |
| blind | `1915_158` | `O(n+m)` | `O(n*m)` | - | `A * n + 2 * A * m + 2 * A + 20` |
| blind | `2650_140` | `O(nlogn)` | `O(n**2)` | - | `50 * n * n + 50 * n + 50` |
| blind | `354_95` | `O(n)` | `O(nlogn)` | - | `a * (2 * CeilLog2(a) + 5) + 10` |
| blind | `794_794` | `O(n)` | `O(n**2)` | - | `20000 * |data| * |data| + 8100000 * |data| + 10` |
| labeled | `1039_15` | `O(nlogn)` | `O(n**2)` | - | `10 * ((ParseInt(n_str)) + 1) * ((ParseInt(n_str)) + 1) + 40 * ((ParseInt(n_str)) + 1) + 40` |
| labeled | `1563_497` | `O(nlogn)` | `O(n**2)` | - | `|values| * |values| + |values| + 10` |
| labeled | `2650_140` | `O(nlogn)` | `O(n**2)` | - | `4 * n * n + 15 * n + 16` |
| labeled | `794_794` | `O(n)` | `O(n**2)` | - | `2000 * |data| * |data| + 6000 * |data| + 1` |

## Declined rather than guessed at a cost

The file is untouched and `notes` says why. These are NOT stubs: the agent read the method, priced the parts it could, and refused the one term the charging convention does not yet cover. They count as not-proved in the rate above, which is right -- no bound was produced -- but the reason is an obstruction in the convention, not a limit of the agent.

- labeled `1047_641` (label `O(n**2)`, guide `v2`)
- blind `1180_626` (label `O(n+m)log(n+m)`, guide `v2`)
- labeled `1180_626` (label `O(n+m)log(n+m)`, guide `v2`)
- blind `1733_64` (label `O(n**2)`, guide `v1`)
- blind `2704_92` (label `O(n**2)`, guide `v1`)

A `v1` decline states its obstacle in prose written under the superseded append charge, so the REASON it gives may be an artifact even though the decline itself stands. blind `1733_64` is the clear case: it argues a cubic true cost from appends "charged real cost |s| per GUIDE.md". Re-run those under v2 before quoting their analysis.

## Verdicts computed under a superseded charge

`s := s + [x]` was charged O(|s|) when these ran. It is O(1) amortised -- the Python backend defers the concatenation, and only an element read of the accumulator inside the same loop forces the flatten that makes the pattern quadratic. Measured; `bigodafny/COMPLEXITY.md` carries the numbers.

An overcharge does not produce a false proof -- the bound still holds. It produces a false DISAGREEMENT: a linear row charged this way lands on a quadratic bound and reads as contradicting an O(n) label. So each bound below is sound and each row needs re-proving, not re-reading. The rows to re-prove first are those whose `direction` is not `equal`: there the overcharge is what put the proof in a different class from the label.

| arm | sid | label | proved | direction | verdict |
|---|---|---|---|---|---|
| blind | `1827_44` | `O(n**2)` | `O(n**2+m**2)` | same-rank | proves |
| labeled | `1827_44` | `O(n**2)` | `O(n**2)` | equal | proves |
| blind | `2650_140` | `O(nlogn)` | `O(n**2)` | looser | proves |
| labeled | `2650_140` | `O(nlogn)` | `O(n**2)` | looser | refutes |
| labeled | `378_20` | `O(n*m)` | `O(n**2)` | same-rank | refutes |
| blind | `794_794` | `O(n)` | `O(n**2)` | looser | proves |
| labeled | `794_794` | `O(n)` | `O(n**2)` | looser | refutes |

7 of 39 graded runs. The manifest keeps the flag it was registered with; this table is computed from the current rule.

## Gate failures

| gate | labeled | blind |
|---|---|---|
| did not verify | 2 | 2 |
| used `assume` | 0 | 0 |
| compiled control flow changed | 1 | 0 |
| behaviour changed | 1 | 0 |
| a `requires` excludes real inputs | 0 | 0 |

## Difficulty: declared before the run vs measured

| difficulty_static | n | proved | mean dafny calls | mean difficulty_measured |
|---|---|---|---|---|
| 1 | 4 | 4 | 2.8 | 2.0 |
| 2 | 18 | 13 | 2.0 | 1.6 |
| 3 | 13 | 9 | 2.8 | 1.9 |
| 4 | 8 | 3 | 5.0 | 2.6 |

## Anti-cheat

- blind examples with a leak attempt: **0**

