# Wave 5

80 rows, `1272_115` .. `2015_168`. All four agents finished; no rate-limit kills.

| batch | agent | audit | tokens | tool calls |
|---|---|---|---|---|
| 1 | 20/20 | **20/20** | 134k | 72 |
| 2 | 20/20 | **20/20** | 95k | 60 |
| 3 | 20/20 | **20/20** | 107k | 54 |
| 4 | 18/20 | **18/20** | 109k | 69 |

Batch 1 included the 8 rows reverted in wave 4; all 8 passed. `1861_28`
reverted after audit.

## The finding: agents reuse one translation across sibling rows

Batch 3 reimplemented `1861_28` with `1861_16`'s DP. All tests passed, and it is
still wrong: the two rows exist *because* their labels differ, O(n**2) vs O(n).

That prompted a dataset-wide scan, now `siblings.py`: per problem, compare the
Dafny of solution pairs whose complexity labels differ.

**49 pairs across 41 problems, involving 87 of 313 translated rows.** Many are
byte-identical Dafny from Python sources with 1-5% text similarity.

Sampling five pairs by reading both Python sources:

| pair | Python A vs B | verdict |
|---|---|---|
| `1092_0`/`1092_11` | `bisect` vs unrolled compares | substitution |
| `565_118`/`565_158` | counting array vs sort+run-length | substitution |
| `1853_66`/`1853_137` | `Counter` dicts vs sort+sweep | substitution |
| `1577_411`/`1577_173` | generator+`try` vs explicit loop | faithful |
| `772_6`/`772_19` | segment tree vs segment tree | faithful |

Three of five are real. Text similarity is not the test: the same algorithm in
different Python styles is faithful, and BigOBench's labels are measured, so
identical algorithms can draw different labels from profiling noise. Each pair
needs its sources read.

All 49 pairs came from one agent, but manifests are ordered by problem id so
siblings always share a batch. That neither proves nor disproves reuse; it does
remove any independent-convergence defence.

## Second harness limit

`1950_45`/`1950_47` take a `real` argument whose tests carry ~100-digit
decimals. `from_str` puts them through Python `float()` first:
`4.6329496401734172195e50` -> `4.632949640173417e50`. No implementation can
pass. Now classified `unvalidatable`. Splits: strict 534, loose 100,
unvalidatable 6.

## Standing

353 valid. The 87 rows in `data/sibling_review.jsonl` need review before this
dataset can claim its labels are sound.
