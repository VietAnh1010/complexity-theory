# Wave 5

80 rows, `1272_115` .. `2015_168`. All four agents finished; no rate-limit kills.

| batch | agent | audit | tokens | tool calls |
|---|---|---|---|---|
| 1 | 20/20 | **20/20** | 134k | 72 |
| 2 | 20/20 | **20/20** | 95k | 60 |
| 3 | 20/20 | **20/20** | 107k | 54 |
| 4 | 18/20 | **18/20** | 109k | 69 |

Batch 1 included wave 4's 8 reverted rows; all passed. `1861_28` reverted.

## Agents reuse one translation across sibling rows

Batch 3 reimplemented `1861_28` with sibling `1861_16`'s DP. All tests passed,
and it is still wrong: the two rows exist *because* their labels differ,
O(n**2) vs O(n).

New `siblings.py` scans dataset-wide for this: per problem, compare the Dafny of
solution pairs whose labels differ. **49 pairs, 41 problems, 87 of 313
translated rows** — many byte-identical Dafny from Python 1-5% alike.

Reading five pairs' sources:

| pair | Python A vs B | verdict |
|---|---|---|
| `1092_0`/`1092_11` | `bisect` vs unrolled compares | substitution |
| `565_118`/`565_158` | counting array vs sort+run-length | substitution |
| `1853_66`/`1853_137` | `Counter` vs sort+sweep | substitution |
| `1577_411`/`1577_173` | generator+`try` vs explicit loop | faithful |
| `772_6`/`772_19` | segment tree vs segment tree | faithful |

Three of five are real. Text similarity is not the test: one algorithm in two
Python styles is faithful, and BigOBench's labels are measured, so identical
algorithms can draw different labels from noise. Each pair needs its sources
read. All 49 came from one agent, but manifests are problem-id ordered so
siblings always share a batch — that neither proves nor disproves reuse.

## Second harness limit

`1950_45`/`1950_47` take a `real` whose tests carry ~100-digit decimals.
`from_str` sends them through Python `float()` first:
`4.6329496401734172195e50` -> `4.632949640173417e50`. No implementation passes.
Now `unvalidatable`. Splits: strict 534, loose 100, unvalidatable 6.

## Standing

353 valid. The 87 rows in `data/sibling_review.jsonl` need review before the
dataset can claim its labels are sound.
