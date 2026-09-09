# Proving the complexity label

`solutions/` proves behaviour: the Dafny reproduces the Python's stdout on
stored tests. It says nothing about the complexity label each row carries. Three
defects found in this project produced correct output, wrong complexity, and
green tests — a doubly-recursive min/max, sibling reuse, and `set<T>` built in a
loop. Testing cannot catch any of them.

`solutions-verified/` proves the label.

## The technique

A **ghost step counter** with a proved upper bound.

```dafny
method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| + 2          // O(n)
{
  steps := 1;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps == 2 * i + 1
    decreases |a_list| - i
  {
    i := i + 1;
    steps := steps + 2;
  }
  output := "";
  steps := steps + 1;
}
```

`dafny verify` discharges the bound. The `ghost` out-parameter is **erased at
compile time** — verified: the emitted Python is `def Solve(n, a__list)` with
zero occurrences of `steps`. So one file both runs under the test harness and
carries a machine-checked complexity proof.

## The counting convention

`steps` charges **1 per elementary operation**, where elementary means constant
time in Dafny's compiled Python:

- arithmetic and comparison on `int`
- `seq` indexing `s[i]` and length `|s|`
- one unit of loop overhead per iteration

Operations that are **not** constant time must be charged their real cost:

| operation | real cost | charge |
|---|---|---|
| `s[i := v]` (seq update) | **O(\|s\|)** — measured, a full copy | `\|s\|` |
| `a[i] := v` on an `array<T>` | **O(1)** — measured, in place | `1` |
| `s + [x]`, appends only | **O(1)** — measured | `1` |
| `s + [x]`, with `s[i]` read between appends | **O(\|s\|)** — measured | `\|s\|` |
| `s + t` (concat) | O(\|t\|) if append-only, else O(\|s\|+\|t\|) | as above |
| `s + {x}` (set insert) | **O(\|s\|)** — measured | `\|s\|`, or avoid it |
| `Join(parts, sep)` | **superlinear** — measured, see below | do not charge; avoid |
| a recursive prelude function over a seq or string | one level per element | its length |
| a call to a helper | its own bound | the helper's `steps` |

### Sequence append is lazy, and reading is what flattens it

Measured in Dafny 4.11.0's Python backend. `s := s + [x]` builds a deferred
concatenation node; the cost lands on whoever forces it. Appending in a loop
that never indexes the accumulator is therefore linear overall, and one later
traversal pays `|s|` once:

    append only        n=8k .053s   16k .067s   32k .095s   64k .149s
    append + |s|       n=8k .062s   16k .070s   32k .101s
    append + s[i]      n=8k .126s   16k .365s   32k 1.725s  64k 7.876s

Taking `|s|` does not flatten — the length is tracked. Reading an element does,
on every append, and that is the quadratic column. So charging `1` per append is
sound **only** under the side condition that no element of the accumulator is
read inside the loop; state it in the file. `3091_384` charges `|row|` per
append instead, which comes to the same total and pays for the one flatten its
second loop forces.

The old table charged `|s|` unconditionally. That was sound — it is an upper
bound on both columns — but it made every accumulate-then-emit row look
quadratic and put its own label out of reach.

### A seq update is a full copy, and Python's is not

`s := s[i := v]` copies the whole sequence. No laziness, and reading or not
reading makes no difference — the opposite of append in both respects. The
Python it translates assigns in place:

    Dafny  s := s[i := v]   n=2k .070s  4k .144s   8k .471s   16k 1.735s
    Dafny  a[i] := v        n=2k .036s  4k .038s   8k .037s   16k .042s
    CPython  lst[i] = v     n=2k .0002s 4k .0002s  8k .0005s  16k .0010s

So a loop that Python runs in O(n) runs in O(n²) once translated with a seq
update. **93 unproved rows contain this pattern.** That is the `set<T>` trap
again, and bigger: correct output, wrong complexity, green tests, and the
label — measured on the Python — is now wrong for the translation rather than
for the algorithm. `CLAUDE.md` § *set<T> is O(n\*\*2)* is the same finding
about a different container, and its remedy applies here: use an `array<T>`
and assign in place.

This one is not a proof obstruction. The cost is known, so the bound is
provable; what it obstructs is the row AGREEING with its label. Charge `|s|`,
prove the quadratic, and record the disagreement as a defect in the
translation, not in the label.

### `Join` is superlinear, so per-line output is deferred

Same backend, `Join` over k five-character parts, pre-flattened, interpreter
startup subtracted:

    n=8k .068s   16k .142s   32k .355s   64k .817s   128k 1.99s

The ratio per doubling settles near 2.3, so the exponent is about 1.2 — above
linear, below quadratic. `SumLen(parts) + |parts|` therefore **undercharges**
it, and undercharging is the one error that voids a proof. Until that cost is
pinned down or the prelude gains a linear-time join, a row whose output is one
line per input item does not get a proof: `171_82`, `89_463`, `2602_57` and
`378_20` are each provable except for this term. Rows printing a single value
are unaffected, which is every proof in `solutions-verified/` so far.

Miscounting here is the whole risk, and it runs both ways. An undercharged
operation turns a real O(n**2) into a proved "O(n)" and Dafny still says
verified; an overcharged one puts a correct label out of reach and invents a
disagreement that is not there. Both were live in this file: the `Join` row is
the first hazard, the old unconditional `|s|` append charge was the second.

## What a proof does and does not claim

**Claims.** The instrumented `steps` is bounded by the stated function of the
input size, for every input satisfying the preconditions. This is a proof over
all inputs, not a measurement on the stored tests.

**Does not claim.** That `steps` equals wall-clock time. The bound is only as
honest as the charging convention above. A reviewer checking one of these files
should check the charges before checking the invariants.

**Relation to the label.** BigOBench's label is synthetic — regression over
profiling runs. A proved bound and the label can disagree, and the proof is the
stronger statement. Where they disagree, record it; do not adjust the proof to
match the label.

## Logarithmic bounds

Dafny has no `log`. `solutions-nlogn/` proves the true O(n log n) for merge sort
with a recursion-tree argument. Two things make it work.

**Match the log's rounding to the code's rounding.** Merge sort splits into
halves of size `ceil(k/2)`, so it wants a CEILING log; a loop that does
`m := m / 2` rounds down, so it wants a FLOOR log —

```dafny
ghost function Log2(x: nat): nat
  decreases x
{ if x <= 1 then 0 else 1 + Log2(x / 2) }
```

— and then `m >= 2 ==> Log2(m / 2) == Log2(m) - 1` holds by definition and the
invariant closes with no lemma at all (`945_255`). Pick the wrong one and the
step is false at some small k and the induction cannot close.

**For a recursive split, that means the ceiling log.**

```dafny
ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }
```

The recursive step is `ceil(n/2)`. Both halves of a split of size k are at most
`ceil(k/2)`, and `CeilLog2(ceil(k/2)) == CeilLog2(k) - 1` then holds *by
definition*. With floor-log that step is false at k = 3: `floor(log2 2) = 1`,
not `floor(log2 3) - 1 = 0`. The induction cannot close.

**Isolate every multiplication.** Z3 does not do nonlinear arithmetic well. The
first attempt timed out at 30s with the whole argument in one `calc`. Splitting
the two multiplication facts into their own lemmas —

```dafny
lemma MulMonoRight(x: nat, p: nat, q: nat) requires p <= q ensures x * p <= x * q
lemma MulDistrib(a: nat, b: nat, k: nat, L: nat) requires a + b == k
  ensures a * L + b * L == k * L
```

— so the solver never has to discover one, took it to 2.8s. The result:

    SortCost(k) <= 2 * k * (CeilLog2(k) + 1) + 1

## Constants

The label is asymptotic, so any constants are acceptable: `steps <= 7*n + 12`
proves O(n). Do not tune constants to look tight — pick whatever the invariant
supports.
