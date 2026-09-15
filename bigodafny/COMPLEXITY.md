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
| `m[k := v]` (map update) | **O(\|m\|)** — measured, a full dict copy | `\|m\|`, or avoid it |
| `m[k]`, `k in m`, `\|m\|` | **O(1)** — measured | `1` |
| `m.Keys`, `m.Values`, `m.Items` | **O(\|m\|)** — measured, materialises a `Set` | `\|m\|` |
| `multiset(s)` | **O(\|s\|)** — measured, `Counter(s)` | `\|s\|` |
| `multiset(a) == multiset(b)` | **O(\|a\|+\|b\|)** — measured | `\|a\|+\|b\|` |
| `\|m\|` on a multiset | O(distinct elements) — `reduce` over keys | distinct count |
| `Join(parts, sep)` | **O(SumLen + \|parts\|)** — measured against a control | `SumLen(parts) + \|parts\|` |
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

### A multiset is linear, unlike the other two

`_dafny.MultiSet` subclasses `collections.Counter`, so `multiset(s)` is `Counter(s)`
and costs one pass. It does **not** share the copying behaviour of `set<T>` and
`map<K,V>` above -- building one is linear, not quadratic:

    n= 1000  0.28ms    n= 4000  0.96ms    n=16000  3.68ms
    n= 2000  0.45ms    n= 8000  1.80ms

Equality is linear too. Rebuilding both sides and comparing, n times over, scales
x4 per doubling -- 477ms / 1878 / 7452 / 29848 / 118190 at n = 1000..16000 -- which
is n comparisons each costing O(n), so one `multiset(a) == multiset(b)` is O(n).

So `multiset(a) == multiset(b)` is a **linear** permutation test, and a row whose
Python reaches the same answer with `sorted(a) == sorted(b)` is O(n log n). That
difference is an algorithm replacement, not a data-structure choice: see
`solutions-tofix/README.md` on the too-fast direction.

One caveat on cardinality: `|m|` on a multiset is `reduce` over the *distinct*
keys, so it is O(distinct), not O(1). The measurement above held the distinct
count at 50 while n grew, and the per-call cost stayed flat at 3.4us -- that
confirms it does not scale with n, not that it is constant in general.

### A map is fast to read and quadratic to build

`map<K,V>` was the last unmeasured entry in this table, and it forced `unsure`
on every audited row whose class depended on it. It is measured now, and it
splits: reads are free, writes are not.

`m := m[k := v]` compiles to `_dafny.Map.set`, which is

    def set(self, key, value):
        map = dict(self)        # <- full copy, every insert
        map[key] = value
        return Map(map)

so building a map in a loop is quadratic. Doubling n quadruples the time:

    n= 1000   10.8ms      n= 4000  163.0ms      n=16000  3988.2ms
    n= 2000   42.8ms      n= 8000 1204.6ms

Same shape and same cause as `s + {x}` above — Dafny's collections are values,
and the Python backend gives a value semantics by copying.

Reads do not copy. `_dafny.Map` subclasses `dict`, so `m[k]`, `k in m` and `|m|`
go straight to the dict and are O(1): n lookups scale as n, 0.1ms at n=1000 and
2.0ms at n=16000.

`m.Keys`, `m.Values` and `m.Items` are the exception among reads — each builds a
fresh `Set`, so each is O(|m|). `|m.Keys|` inside a loop is quadratic where
`|m|` is constant.

    |m| in a loop, n times:        0.1ms / 0.1ms / 0.3ms  (n = 1000 / 2000 / 4000)
    |m.Keys| in a loop, n times:  10.8ms / 49.3ms / 172.6ms

For reference on the same machine, an `array<int>` of n elements fills in
0.3 / 0.5 / 1.0ms — linear, and about 160x faster than the map build at n=4000.
A row that needs a keyed structure it writes to in a loop wants an array or a
sorted `seq` with binary search, not a `map`.

### `Join` is linear — and how the opposite got recorded first

`Join` costs `SumLen(parts) + |parts|`. Charge it; per-line output is not
blocked.

This entry replaces the opposite claim, which stood in this file for part of one
session and cost four agent runs. The error is worth keeping because it is the
one the rest of this document warns about, committed by the person warning:

    Join           n=32k .343s  64k .783s  128k 1.706s  256k 3.442s
    linear control n=32k .128s  64k .308s  128k  .714s  256k 1.597s

The first reading took Join's ratios of ~2.2 per doubling as an exponent of
about 1.2 and called it superlinear. But the **control** — one pass summing
`|parts[i]|`, indisputably linear — shows ratios of 2.40, 2.32, 2.24 in the
same harness. A ratio near 2.2 is what linear looks like here; the excess is
constant overhead, not growth. Join's ratios are *lower* than the control's at
every size, and the join÷control ratio falls from 2.68 to 2.16 as n grows.

Two rules follow, and they are the point of the entry:

- **Measure against a control, not against 2.0.** An exponent read off raw
  ratios in a noisy harness is not a measurement. Nothing here should be called
  superlinear again without a known-linear baseline beside it in the same table.
- **Overcharging is not the safe direction.** Refusing to charge Join looked
  conservative. It blocked 164 rows, sent four agent runs to a decline they did
  not need, and manufactured an obstruction that was never there. This document
  says an overcharge invents a false disagreement; that is what happened.

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
