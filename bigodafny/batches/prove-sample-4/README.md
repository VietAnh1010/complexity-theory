# `prove-sample-4/` — 38 of 50, and the campaign-3 crossover does not hold

50 rows from the 211 in `solutions/` that carry a label, pass their gate, and
had no proof. Seed **2026092103**. Three Sonnet agents, one slice each,
**3 attempts and 5 minutes per row**.

**Result: 38 proved, 12 unresolved.** `proofs.py` re-verified the whole overlay
from scratch — 189/189 files verify, 0 contain `assume` — `audit.py` found no
disagreement with the verifier, and `precheck.py` checked every proved row's
preconditions against real inputs: 74 clauses, 0 violated.

## What this campaign overturns

Campaign 3's README was titled *the label stops predicting difficulty*. It is
withdrawn. This draw did not reproduce it.

| label | c1 | c2 | c3 | c4 | pooled |
|---|---|---|---|---|---|
| `O(n)` | 24/24 | 20/23 | 12/18 | **21/25** | 77/90 = **86%** |
| `O(nlogn)` | 5/11 | 7/11 | 10/12 | **7/10** | 29/44 = **66%** |
| `O(n**2)` | 5/6 | 3/7 | 6/9 | 7/11 | 21/33 = 64% |
| `O(1)` | 4/5 | 3/3 | 8/8 | 3/4 | 18/20 = 90% |

Pooled, `O(n)` is 86% and `O(nlogn)` 66% — campaign 1's ordering, and far less
extreme than 24/24 against 5/11 made it look. Campaign 3's `O(n)` cell tests at
**p = 0.036** against the pooled rate, which does not survive the eight
comparisons this table invites the eye to make. Its `O(nlogn)` cell is p = 0.24:
plain noise.

The mistake was structural, not arithmetic. A label class holds 8 to 25 rows
per campaign, so two rows move a rate by ten points, and three points on a line
look like a trend. `collect.py` now computes `campaign_series`, which reports
the pooled rate and a per-cell binomial test, so the next reader gets the test
without having to think of it.

## What survives: the obstacle, not the rate

| obstacle | c3 | c4 |
|---|---|---|
| `value-to-size` | 4/11 | **5/12** |
| `z3-nonlinear` | 3 | 4 |
| `invariant-gap` | 2 | 2 |
| `decreases-star` | 2 | 1 |

`value-to-size` is connecting a cost bounded by an input **value** back to a
bound in the row's size. This campaign's agents named it independently — none
had seen campaign 3 — in three separate phrasings:

> a per-call cost that depends on something other than the outer loop index
> value-bounded quantities that need scaffolding before the ensures can be stated
> a genuinely value- not size-bounded sqrt search

The five: `1306_126` (guard calls a sum inline), `1948_388` (`while s*s < target`),
`2423_48` (trip count is a raw value off sorted data, and the prelude has no
sortedness lemma to name it), `2819_926` (value-bounded `CeilLog2` cost),
`2926_50` (a 53-term literal-prime product).

A recurring named obstacle is a better finding than a moving rate. It does not
depend on a cell of 12.

## Relations

| relation | rows | |
|---|---|---|
| `confirms` | 34 | the bound is within the label's class |
| `looser-structural` | 3 | the proof exposes a cost the label omits |
| `looser-slack` | 1 | a loose scaffold, tight bound not attempted |

All four non-`confirms` rows were re-read against their Python. **The relations
stood; two of the reasons did not**, and are rewritten in
`label_relation.jsonl` with `reason_rewritten: true`:

- `2358_421` — the agent said `IntSqrt2358b` costs `O(v)` per call. It
  increments `r` until `(r+1)^2 > v`, so it runs `floor(sqrt(v))` times. `O(v)`
  is the *proof's* bound, not the algorithm's: the invariant bounds `r` by `x`
  rather than by `sqrt(x)`. The structural point stands — the `O(n)` label omits
  a sum-of-roots-of-values term — but the row is slack as well as structural.
- `1820_180` — the agent said the window is bounded only by `|d_list|`. The
  Python takes `min(arr[i-x : i+y+1])`, so the window is `x + y + 1`, two input
  **values**, and the true cost is `O(n*(x+y))`. `|d_list|` is the proof's
  over-approximation.

`276_610` is `looser-structural` for `IntToString`'s digit-length charge on
printed values — the same shape as `2381_156`, one of the four rows moved to
`solutions-disputed/` under the value-versus-size convention. **It has not been
moved.** That decision named a specific set of rows and this is not one of them.

## The draw was the narrowest yet

Four label classes only: `O(n)` 25, `O(n**2)` 11, `O(nlogn)` 10, `O(1)` 4. No
`O(n+m)`, no `O(logn)`, no compound labels — three campaigns drained them.

Six rows had been drawn and failed before, so they returned to the pool for an
independent retry: `1765_40`, `1820_180`, `2036_120`, `2423_48`, `2819_926`,
`2854_30`. That is 12% of the draw against 8% in campaign 3. Of the six, three
closed this time (`1765_40`, `1820_180`, `2036_120`) and three failed again —
`2423_48`, `2819_926` and `2854_30`, each for the reason it failed before,
found by an agent that had not seen the earlier attempt.

As the pool shrinks the residue concentrates, and a growing share of each draw
is rows already known to be hard. That pushes the rate down for reasons that
have nothing to do with the agents, and it is another argument for reading the
pooled column.

## Files

| file | what it is |
|---|---|
| `manifest.jsonl` | the 50 rows: id, path, label, split, gate |
| `slice_{a,b,c}.jsonl` | the three agent assignments, 17/17/16 |
| `PROMPT_{a,b,c}.md` | the agent briefs |
| `traj_{a,b,c}.jsonl` | per-row attempts, bound, timing, failure reason |
| `label_relation.jsonl` | normalised relation per proved row, with reasons |
| `obstacles.jsonl` | coded obstacle per unresolved row |
| `audit.jsonl`, `summary.json` | the verifier-joined audit and its totals |

Bounds in `label_relation.jsonl` are read from each file's `Solve` method, not
from `data/complexity_proofs.jsonl`, whose `bound_of` takes the first
`ensures steps <=` in a file — a helper's in 7 of the proofs.
