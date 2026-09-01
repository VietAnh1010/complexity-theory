# Wave 6 (batches 2-4; batch 1 still running)

60 rows, `2105_521` .. `2577_822`. Added **Rule Zero** to the prompt: never
reuse a translation between two solutions of one problem.

| batch | agent | audit | tool calls |
|---|---|---|---|
| 2 | 20/20 | **20/20** | 50 |
| 3 | 20/20 | **20/20** | 61 |
| 4 | 20/20 | **20/20** | 32 |

## Rule Zero worked

| | pairs flagged | rows | rate per 100 rows |
|---|---|---|---|
| Waves 1-5 | 49 | 313 | 15.7 |
| Wave 6 | 2 | 60 | **3.3** |

A five-fold drop. And both wave-6 hits are pairs the agent itself declared
genuinely identical: `2325_570`/`2325_862` ("same trivial extraction, differs
only in unpacking style") and `2577_283`/`2577_822` ("same arithmetic result",
one summing a variable-length row, the other unpacking 3 fixed fields).

Asking each agent to *enumerate its sibling pairs and say how the algorithms
differ* is what changed the behaviour. Batch 2 found 8 pairs, batch 3 nine,
batch 4 nine — each with a concrete distinction:

- `2185_148`/`2185_274` — try every candidate offset against a hash set O(n**2),
  vs exploit that all offsets are equal and average coordinates O(n).
- `2482_13`/`2482_151` — brute-force `while` counter, vs closed-form ceiling
  division.
- `2286_14`/`2286_319` — O(1) falling-factorial identity, vs three O(n)
  factorial calls.
- `2358_103`/`2358_421` — sort then scan, vs one unsorted pass tracking a
  running max.

Batch 3 also reported two pairs as *genuinely the same algorithm* rather than
inventing a difference. That honesty is the point: the rule is meant to stop
reuse, not to force fabricated distinctions.

## Input-mapping trap, again

`2505_30`/`2505_87` have signature `coordinates: seq<seq<int>>` while the Python
reads one line of n ints. The generic `from_str` wraps that single line as
`coordinates[0]`. Third instance of the dataclass not matching a literal read of
the Python, after problem 1073's off-by-one `n` and `1306`'s unaggregated list.

## Carried forward

Prelude candidates named by agents: `Power`/integer exponent, and a
`RepeatInt(v, n)` since `Repeat` is string-only and `seq(n, _ => 0)` is easy to
get wrong. Neither added mid-wave.
