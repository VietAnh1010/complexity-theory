# Label audit — one batch

You are auditing whether a row's stated complexity label describes what its
**Dafny** actually costs. You are not writing proofs and not editing any row.

Read `BATCH_FILE`. It is a JSON array of ~20 rows, each with:

    sid, label, path, facts (deterministic), dafny (full source),
    python (source), description (the problem statement)

`description` is the authority for any loop bounded by a VALUE rather than a
size. Quote the constraint from it rather than assuming a contest convention.

Write one JSON object per row to `OUT_FILE`, one per line (JSONL). Write nothing
else, anywhere. Do not modify any `.dfy`. Do not run `dafny`.

## The cost model — stipulated, not measured

> **This table changed on 2026-09-16.** Every `verdicts_*.jsonl` file in this
> directory — all 25 — was filed against a table read off Dafny's Python
> backend, in which `s[i := v]`, `m[k := v]` and set insertion were all linear. They are `1` now. Do not compare a verdict
> from an earlier batch against one filed under this table without checking
> which model it used. `bigodafny/COMPLEXITY.md` has the full model and the
> reasoning; the short version is that the labels were measured on CPython, so
> a model derived from Dafny's Python backend compared two unrelated
> implementations and called the difference a translation defect.

Charge 1 for: `int` arithmetic and comparison, `s[i]`, `|s|`, one unit of loop
overhead per iteration.

Everything else costs what the table says:

| operation | cost | note |
|---|---|---|
| `s := s[i := v]` (seq update) | O(1) | as CPython's `lst[i]=v` |
| `s := s + [x]` | O(1) amortised | |
| `s + t` (concat) | O(\|t\|) | |
| `s[a..b]` (slice) | O(1) | a view |
| `s := s + {x}` (set insert), `x in s` | O(1) | as CPython's `set` |
| iterating a `set` | O(\|s\|) | |
| `m[k := v]`, `m[k]`, `k in m`, `\|m\|` | O(1) | as CPython's `dict` |
| `m.Keys`, `m.Values`, `m.Items` | **O(\|m\|)** | each materialises a fresh collection |
| `multiset(s)` | O(\|s\|) | one pass |
| `multiset(a) == multiset(b)` | O(\|a\|+\|b\|) | a **linear** permutation test |
| `Join`, `JoinInts` | O(total output length) | linear |
| `SumSeq`, `MaxSeq`, `MinSeq`, `ParseInt`, `SplitWs`, `ReplaceAll`, `Repeat`, `IntToString` | O(length of the argument) | recursive over the sequence/string |
| `SortInts`, `SortStrings`, `Sort` | O(k log k) | merge sort |
| a hand-written recursion on `s[1..]` | O(\|s\|) | one level per element; the slice itself is free |
| `int` ops where the value grows with n (factorials, `2**n`) | not O(1) | bignum |

`array<T>` is not in this table because it is not in the corpus. Two rows keep
one for reasons about the backend, not the model; see `COMPLEXITY.md`'s
appendix.

## What this rules out as a verdict

A row is **not** a `translation` defect because a Dafny collection copies where
CPython assigns in place. That was the largest class in earlier batches — 93
rows at its peak — and it no longer exists. If your evidence for `cause:
"translation"` is "the seq/map/set update copies", the verdict is `ok`.

`cause: "translation"` still applies, and these are the shapes that matter:

- **An algorithm replaced.** The Dafny reaches the answer a different way, so it
  is in a different class — including a *better* one. `multiset(a) ==
  multiset(b)` where the Python does `sorted(a) == sorted(b)` is linear against
  the Python's O(n log n). See `solutions-disputed/README.md` on the too-fast
  direction.
- **Slicing.** CPython's `a = a[1:]` copies; Dafny's `s[1..]` is a view. A row
  whose Python peels a list in a loop is genuinely quadratic while its
  faithful-looking translation is linear. `2087_50` is the case.
- **A concat rebuilt at every level.** `f(s[1..]) + [x]` is quadratic because of
  the concat, not the slice — `888_6`.
- **A library call reimplemented.** `Log2Floor` looping where Python calls
  `math.log2` once is real per-call overhead the translation introduced.

## What counts as a mismatch

Compare the label against the tight class of the **Dafny**, in the input sizes
the signature exposes.

- A label naming a dimension the code never scans is wrong. `O(n*m)` on a body
  that reads `row[0]` and `row[1]` and never walks a row is O(n): row width does
  not enter the cost.
- A label naming a growth rate no construct exhibits is wrong. `O(n**2)` on
  straight-line code with no loop and no recursion over a collection is O(1) or
  linear in the input text.
- A loop bounded by a **value** rather than a size is not automatically wrong —
  if the problem statement caps that value, the cost is constant in the input
  size. Say so rather than calling it unbounded.
- Same growth rank under different names is **not** a mismatch. `O(n*m)` vs
  `O(n**2)` where n and m are the two halves of the same input, or
  `O(n**2)` vs `O(n**2+m**2)`, are naming choices. Verdict `ok`.

## The two causes — getting this right is the point of the audit

When the Dafny does not match the label, decide which is at fault by comparing
against the **Python**, which is what the label was measured on:

- `cause: "label"` — the Python is not the labelled class either. The label is
  wrong and the translation is faithful.
- `cause: "translation"` — the Python **does** match the label but the Dafny
  does not. Under the current table this means the translation changed the
  algorithm, not the container: see § *What this rules out as a verdict* for
  the four shapes that qualify. A seq, map or set update in a loop does **not**.
  Here the label is right about the program it was measured on.
- `cause: "harness"` — **the label is right about the Python and the Dafny is
  right too; the difference is where the dataset drew the boundary.** The Python
  reads stdin and pays to parse every input; the Dafny's `Solve` receives those
  inputs already parsed as arguments, so parsing is outside the measured method.
  A Python that does `b = list(map(int, input().split()))` and then reads only
  `b[0]` is genuinely O(n+m); the Dafny that takes `b_list` and reads `b_list[0]`
  is O(n). Nothing is wrong with either. Check for this whenever an input is
  declared in the signature but barely indexed — it is not a label error.
- `cause: "both"` — neither matches.

## Output schema — one line per row, all fields required

```json
{"sid": "2087_50", "label": "O(n**2)", "verdict": "mismatch",
 "true_class": "O(n)", "cause": "translation", "confidence": "high",
 "what_to_look_for": "The label was measured on a Python that does `a = a[1:]` in a loop, which copies, so the Python really is quadratic. Open the Dafny and check whether it peels with `s[1..]`; a Dafny slice is a view, so the same loop is linear and the translation is in a BETTER class than the program the label describes.",
 "evidence": "The Dafny peels with s := s[1..] inside a loop over n elements. A seq slice is a view and costs O(1), so the loop is O(n) total; the Python's a = a[1:] copies the remaining n-i elements at every step and is O(n**2) as labelled. The translation is faithful line for line and still lands a class faster, which is the algorithm-replacement shape, not a container difference.",
 "auditor": "labelaudit-batch-NN"}
```

- `verdict`: `ok` | `mismatch` | `unsure`
- `true_class`: the tight class of the Dafny, in the signature's sizes.
  **It must be one of these eleven strings, copied exactly** — this is the
  dataset's whole vocabulary and anything else is rejected:

      O(1)   O(logn)   O(n)   O(nlogn)   O(n**2)   O(n*m)
      O(n+m)   O(n+m)log(n+m)   O(n+mlogm)   O(nlogn+mlogm)   O(n**2+m**2)

  plus `other` — use it, with the real class named in `evidence`, when the true
  cost is outside that vocabulary: cubic, or a cost in a VALUE rather than an
  input size. Forcing such a row into the nearest listed class loses the finding.

  When the verdict is `ok`, `true_class` must equal `label` exactly.
  When the verdict is `unsure`, give your best single candidate from the list
  anyway — never the word "unsure".
- `cause`: `label` | `translation` | `harness` | `both`. Use `""` for `ok`.
- `confidence`: `high` | `medium` | `low`.
- `what_to_look_for`: **required on every `mismatch` and `unsure`.** Written for
  a human who will open the file and decide. Two things, in order: (1) the
  specific way the current label could be wrong, stated as a claim they can
  refute; (2) the concrete check that settles it — the identifier to find, the
  `requires` to read, the line of Python to compare, the input field whose width
  to measure. Not a restatement of the evidence: the evidence says what you
  concluded, this says what would confirm or overturn it. Example: "The label
  assumes row width varies. Open the problem statement and check whether a row
  is always a fixed-width tuple; if the input format pins it, m is a constant
  and the label is wrong. If rows can be ragged, the label stands."
- `evidence`: one or two full sentences, **at least 12 words**, naming the
  identifier and the construct. A reviewer must be able to open the file, find
  what you named, and check the claim. "Nested data loops" and "value-bounded
  loop, likely O(1)" are rejected: they name nothing and assert a guess.
- `cause` must be consistent with the code. `translation` claims the Python and
  the Dafny are in different classes, so it requires a construct in the Dafny
  that CPython does not pay for. A row with no loops cannot have a translation
  fault; neither can one whose Dafny mirrors the Python operation for operation.

## Read the Python before assigning a cause

`cause` is the field auditors get wrong, and both directions have happened:

- `685_583` was called a label error because its Dafny takes a maximum with two
  linear scans and never sorts. Its **Python** does `sorted(a)` then `a[-1]`, so
  the O(nlogn+mlogm) label is correct and the translation dropped the sort.
- `396_361` was called a translation error because its Python calls
  `max(dimensions[i])` while the Dafny reads `row[0]` and `row[1]`. But a
  "rectangle" row holds exactly two numbers, so that `max` is O(1) and the
  Python is O(n): the O(n*m) label really is wrong.

The difference is never visible in the Dafny alone. Before writing `translation`
you must find the construct in the **Python** that costs more than the Dafny's,
and check what its data actually contains — a `max()` over a two-element row is
not an m-dimension. Before writing `label` you must be satisfied the Python does
not pay that cost either.

**A sibling with a different label is not evidence of an error.** Two solutions
of one problem are kept precisely because they differ. `685_777` really is
O(n+m) and `685_583` really is O(nlogn+mlogm) — the Pythons differ by a sort.
Use a sibling as a prompt to read both sources, never as the argument itself.

If you cannot settle the cause from the two sources, keep `verdict: "mismatch"`
and set `confidence: "low"`; say in the evidence which way you lean and why.

## When the label matches the Dafny by accident

A row can be `ok` for the wrong reason. `888_6` is labelled O(n**2) and its
Dafny is O(n**2) -- but only because `ReverseSeq` slices `s[1..]` and
concatenates at every level. The Python's `D[::-1]` is O(n) and everything
around it is O(n), so the Python is linear. The label describes the Dafny, and
the two agree by coincidence.

Set `"translation_defect": true` on any row where the **Dafny** is in a worse
class than the **Python**, whatever the verdict. On a `mismatch` it usually
accompanies `cause: "translation"`. On an `ok` it is the only way the row gets
seen at all: the verdict stays `ok`, and the flag says the agreement is
accidental. Omit the field entirely when the translation is faithful.

## Your output is machine-checked

`checkverdicts.py` validates every line against the schema above and
cross-checks any row that has a machine-checked proof in the repository. A batch
with schema violations is discarded unread, and a verdict that contradicts a
proof is treated as evidence the auditor is unreliable. Getting the vocabulary
and the evidence right is not formatting: it is what makes the batch usable.

## Rules

- **Answer `unsure` when you are not sure.** These verdicts feed a human review
  queue. A wrong `mismatch` costs a reviewer more than a missed one; a queue
  full of false positives is worse than a short queue.
- Never answer `mismatch` on a same-rank naming difference.
- Judge only from the `dafny`, `python` and `facts` given. Do not open other
  files, do not search the repository, do not run anything.
- Every row in the batch gets exactly one line in the output, including the ones
  you mark `unsure`. The counts must match.
- Report at the end: how many `ok` / `mismatch` / `unsure`, and the two rows you
  were least certain about.
