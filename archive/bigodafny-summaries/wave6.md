# Wave 6

80 rows, `1861_28` .. `2577_822`. Added **Rule Zero**: never reuse a translation
between two solutions of one problem.

| batch | agent | audit | tool calls |
|---|---|---|---|
| 1 | 20/20 | **20/20** | 86 |
| 2 | 20/20 | **20/20** | 50 |
| 3 | 20/20 | **20/20** | 61 |
| 4 | 20/20 | **20/20** | 32 |

`1861_28` — the row that exposed the defect — was retranslated from its own
Python. Similarity to its sibling fell **1.00 -> 0.25**.

## Rule Zero worked

| | flagged pairs | rows | rate per 100 rows |
|---|---|---|---|
| Waves 1-5 | 49 | 313 | 15.7 |
| Wave 6 | 2 | 80 | **2.5** |

Both wave-6 hits are pairs the agents themselves declared genuinely identical
(`2325`: differs only in unpacking style; `2577`: same arithmetic, different row
handling). Batch 3 likewise reported two pairs as the same algorithm rather than
inventing a difference — the rule stops reuse without forcing fabrication.

What changed the behaviour was requiring each agent to *enumerate its sibling
pairs and say how the algorithms differ*. Examples returned:

- `2185_148`/`274` — offsets against a hash set O(n**2), vs averaging O(n)
- `2286_14`/`319` — O(1) falling-factorial identity, vs three O(n) factorials
- `2051_25`/`80` — one scan tracking running min, vs suffix-max array + bisect

## `set<T>` builds in O(n**2)

An agent hit a 100% CPU hang and diagnosed it. Verified with a microbenchmark:

    n=2000 0.017s   n=4000 0.070s (4.1x)   n=8000 0.278s (4.0x)

against `seq` at 0.004 / 0.006 / 0.011s. Dafny's Python runtime backs `set<T>`
with a frozenset, doing an incremental union per insert.

This corrupts complexity labels, not just speed: a set built in a loop adds a
factor of n while the tests, being small, still pass. Same shape as the
doubly-recursive min/max trap. **19 translations use `set<>`** and should be
reviewed. Recorded in `CLAUDE.md`.

## Standing

433 of 534 strict rows valid (81%). 101 remain. The 91 pre-Rule-Zero rows in
`data/sibling_review.jsonl` still need review.
