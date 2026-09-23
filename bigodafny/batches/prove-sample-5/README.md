# `prove-sample-5/` — 37 of 50, two proofs destroyed, one bug of mine

50 rows from the 179 in `solutions/` that carry a label, pass their gate, and
had no proof. Seed **20260922**. Three Sonnet agents, one slice each,
**3 attempts and 5 minutes per row**.

**Result: 37 proved, 13 unresolved** — but read the next section before
quoting that number.

`proofs.py` re-verified the whole overlay from scratch (225/225 files verify, 0
contain `assume`), every new proof was run through `dafny verify` here, and
`audit.py` reports no disagreement with the verifier.

## Three things went wrong, and two of them were mine

**1. A sampler bug let already-proved rows back into the pool.**
`sample.py` built its "already proved" set from a flat listing of
`solutions-proved/<pid>/` plus an explicit mention of `nlogn/`. When
`value-bounded/` was created the day before, nothing added it, so the 12 rows
moved there rejoined the pool as if unproved. This draw redrew two.

- `2128_34` — pure waste. The agent worked the row before noticing the existing
  proof and stopping.
- `305_76` — **not** waste. The second attempt produced a strictly tighter
  bound: the tight `CeilLog2` recursion tree for both sorts instead of the
  quadratic `SortCost` scaffold, with the value term isolated as
  `4 * AbsInt(SortInts(d_list)[0])`. It replaced the original.

So the rate over genuinely new rows is **35 of 48**, not 37 of 50. Fixed:
`dfy_files_deep` walks the overlay at any depth, so a new variant
subdirectory cannot leak proved rows back.

**2. Two verified proofs were deleted by agents.** Both times an agent
cleaning up after its own *failed* row removed a proof for a **different
solution of the same problem**:

| destroyed | by an agent abandoning | in slice |
|---|---|---|
| `2914_264` | `2914_3` | C |
| `750_51` | `750_14` | C |

Both restored from `HEAD` and re-verified. The first was caught only by reading
`git status`; the second was caught by the check added because of the first.
`audit.py` now fails on any deletion under `solutions-proved/` whose row is not
in the batch.

This is the trap `CLAUDE.md` names under *"two solutions of one problem"* — a
shared problem directory, different labels — appearing as a filesystem hazard
rather than a modelling one.

**3. A trajectory was not JSONL.** Slice C wrote pretty-printed JSON across 59
lines for 16 rows. No data was lost; every consumer simply raised instead of
reporting. Repaired with `raw_decode`, content untouched, and `audit.py` now
names the offending line instead of crashing.

## Rates

| label | c1 | c2 | c3 | c4 | c5 | pooled |
|---|---|---|---|---|---|---|
| `O(n)` | 24/24 | 20/23 | 12/18 | 21/25 | 22/27 | 99/117 = **85%** |
| `O(nlogn)` | 5/11 | 7/11 | 10/12 | 7/10 | 8/13 | 37/57 = **65%** |
| `O(n**2)` | 5/6 | 3/7 | 6/9 | 7/11 | 4/6 | 25/39 = 64% |
| `O(1)` | 4/5 | 3/3 | 8/8 | 3/4 | 1/1 | 19/21 = 90% |

Five campaigns in, the pooled rates have barely moved and campaign 1's ordering
holds. The crossover reported after campaign 3 remains withdrawn.

The pool is down to 179 and its residue is concentrating: **10 of these 50 rows
had been drawn and failed in an earlier campaign** — 20%, against 12% in
campaign 4 and 8% in campaign 3. (The figure quoted when this batch was drawn,
24%, counted the two redrawn rows above; it was wrong.)

## Obstacles

| obstacle | rows |
|---|---|
| `value-to-size` | 5 |
| `z3-nonlinear` | 4 |
| `invariant-gap` | 2 |
| `decreases-star` | 1 |
| `prelude-gap` | 1 |

`prelude-gap` is a new code, and it is the same shape as the problem
`SortIsSorted` solved: `1582_315` needs a histogram partition-sum lemma
(`SeqSum` over 26 buckets equals `|v_1|`) and a `Repeat`-length lemma, and
**neither exists in the prelude**. Unlike `value-to-size`, that kind of gap is
fixable once for every row that hits it — which is what made `2423_48`
provable this week.

`457_38` failed for the fourth campaign running, every time for the same
reason: the source carries `decreases *`.

## The cost-model family now has four members

`1359_4` is `tighter-costmodel`, checked against the Python rather than taken
from the agent's report. Three loops run `h *= i` with **no** mod inside them —
the reduction is only at the final `print` — so `h` grows to factorial scale
and CPython's multiply cost grows with its digit count. The charge table costs
every `int` operation 1, so the proof comes out linear in the value `a` where
the label says `O(n**2)`.

That is the fourth row where the label and the charge table diverge, and every
one of them builds an **unreduced integer product**: `2803_133`, `1073_645`,
`2496_30`'s helper, and now `1359_4`. The divergence is not scattered; it has a
signature.


## Revised 2026-09-23

The prelude gained a composable sort-cost bound and a binary-search potential
(`SortCostNLogN`, `SortCostWithin`, `SearchPot`, `BisectStep`,
`SearchLoopWithin`). With them these rows were re-proved or newly proved, by
hand and outside this campaign's budget:

| row | label | this campaign | now |
|---|---|---|---|
| `1582_118` | O(nlogn) | unresolved | proved, `confirms` |
| `1827_66` | O(nlogn) | unresolved | proved, `confirms` |
| `2128_34` | O(n**2) | proved, `looser-structural` | proved, `looser-structural` |

**The numbers in this README are unchanged**: they are what a bounded agent
achieved. Each revised trajectory keeps the agent's result as `agent_outcome`,
`agent_relation` and `agent_bound`, and every superseded line — trajectory,
relation, obstacle, audit — is in `old_record.jsonl`, with the file it came
from.

## Files

| file | what it is |
|---|---|
| `manifest.jsonl` | the 50 rows: id, path, label, split, gate |
| `slice_{a,b,c}.jsonl` | the three agent assignments, 17/17/16 |
| `PROMPT_{a,b,c}.md` | the agent briefs, including the new prelude lemmas |
| `traj_{a,b,c}.jsonl` | per-row attempts, bound, timing, failure reason |
| `label_relation.jsonl` | normalised relation per proved row, with reasons |
| `obstacles.jsonl` | coded obstacle per unresolved row |
| `audit.jsonl`, `summary.json` | the verifier-joined audit and its totals |
| `old_record.jsonl` | every line superseded by the 2026-09-23 revision, with its source file |
