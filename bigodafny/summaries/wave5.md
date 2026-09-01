# Wave 5

80 rows, `1272_115` .. `2015_168`. All four agents finished; no rate-limit kills.

| batch | agent | audit | tokens | tool calls |
|---|---|---|---|---|
| 1 | 20/20 | **20/20** | 134k | 72 |
| 2 | 20/20 | **20/20** | 95k | 60 |
| 3 | 20/20 | **20/20** | 107k | 54 |
| 4 | 18/20 | **18/20** | 109k | 69 |

Batch 1 included the 8 rows reverted in wave 4; all 8 passed this time.
1 row (`1861_28`) reverted after audit — see below.

## The finding: agents reuse one translation across sibling rows

Batch 3 reimplemented `1861_28` with `1861_16`'s DP. All tests passed. It is
still wrong: those two rows exist *because* their labels differ, O(n**2) vs
O(n). The Dafny became an O(h*w) DP under an O(n**2) label.

That prompted a dataset-wide scan, now `siblings.py`: for each problem, compare
the Dafny of solution pairs whose complexity labels differ.

**49 pairs across 41 problems, involving 87 of 313 translated rows.** Many are
byte-identical Dafny from Python sources with 1-5% text similarity.

Sampling five pairs by reading both Python sources:

| pair | Python A | Python B | verdict |
|---|---|---|---|
| `1092_0`/`1092_11` | `bisect` binary search | unrolled linear compares | substitution |
| `565_118`/`565_158` | counting array O(n) | sort + run-length O(nlogn) | substitution |
| `1853_66`/`1853_137` | `Counter` dicts | sort + sweep | substitution |
| `1577_411`/`1577_173` | generator + `try` | explicit loop | faithful |
| `772_6`/`772_19` | segment tree | segment tree | faithful |

Three of five are real. Text similarity alone is not the test — same algorithm
in different Python styles is faithful, and BigOBench's labels are measured, so
two identical algorithms can still get different labels through profiling noise.
Each pair needs its sources read.

All 49 pairs were produced by the same agent. That is guaranteed by construction
— manifests are ordered by problem id, so siblings always land in one batch — so
it neither proves nor disproves reuse. It does remove any independent-convergence
defence.

## Second harness limit

`1950_45`/`1950_47` take a `real` argument whose tests carry ~100-digit
decimals. `from_str` puts them through Python `float()` first:
`4.6329496401734172195e50` -> `4.632949640173417e50`. No implementation can
pass. Now classified `unvalidatable`. Splits: strict 534, loose 100,
unvalidatable 6.

## Standing

353 valid. The 87 rows in `data/sibling_review.jsonl` need review before this
dataset can claim its labels are sound.
