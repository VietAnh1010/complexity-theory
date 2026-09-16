# The cost model, and proving a complexity label

Two things live here, and they are separate:

1. **The cost model** — what a Dafny operation is charged. Stipulated, not
   measured. This is what an audit verdict and a proof are both written against.
2. **The proof technique** — a ghost step counter with a proved upper bound,
   which is how `solutions-proved/` turns a label into a checked claim.

`solutions/` proves behaviour: the Dafny reproduces the Python's stdout on
stored tests. It says nothing about the label. Three defects found in this
project produced correct output, wrong complexity, and green tests — a
doubly-recursive min/max, sibling reuse, and `set<T>` built in a loop. Testing
cannot catch any of them.

## 1. The charges are stipulated

Charge **1** for each of:

- arithmetic and comparison on `int`
- `seq` indexing `s[i]` and length `|s|`
- one unit of loop overhead per iteration

Charge the collections their **standard asymptotic cost**, as an axiom,
independent of any backend:

| operation | charge | |
|---|---|---|
| `s[i]`, `\|s\|` | `1` | |
| `s[i := v]` | `1` | as CPython's `lst[i] = v` |
| `s + [x]` | `1` | amortised |
| `s + t` | `\|t\|` | |
| `s[a..b]` | `1` | a view |
| `m[k]`, `k in m`, `m[k := v]`, `\|m\|` | `1` | hash semantics, as CPython's `dict` |
| `m.Keys`, `m.Values`, `m.Items` | `\|m\|` | materialises |
| `x in s`, `s + {x}` on `set<T>` | `1` | as CPython's `set` |
| iteration over a set | `\|s\|` | |
| `multiset(s)` | `\|s\|` | |
| `multiset(a) == multiset(b)` | `\|a\|+\|b\|` | |
| `Join(parts, sep)` | `SumLen(parts) + \|parts\|` | |
| a recursive prelude function over a seq or string | its length | one level per element |
| a call to a helper | the helper's `steps` | |

`array<T>` is absent because the corpus is. Two rows keep one; see the appendix.

### Why stipulated and not measured

Every entry above was once justified by reading
`DafnyRuntimePython/_dafny/__init__.py` and timing the emitted Python. That made
the model true of *one backend at one version* and nothing else. Three
consequences we actually hit:

- The model changed four times in one session — map, multiset, slicing,
  `Std.Strings.ToNat` — and each change invalidated verdicts already filed.
- A row's class depended on which backend you compiled for. `m[k := v]` is a
  `dict(self)` copy in Python and something else in C# or Java.
- **The labels come from BigOBench measuring CPython.** A model derived from
  Dafny's Python backend was comparing two unrelated implementations and calling
  the difference a translation defect.

So the charges above are the model a complexity-theory reader expects, and the
one the labels were measured against.

### What it costs, stated plainly

**The axioms are false of the artifact we ship.** A row charged O(n) can take
O(n²) of wall-clock under `dafny translate py`. The appendix records exactly
where and by how much, because that is not a footnote — twice it decides
whether a row can run at all.

The consequence for the pipeline: `validate.py` and `difftest.py` check
**behaviour only**, and nothing checks the complexity claim except the
hand-written proofs in `solutions-proved/`. That is the intended design. A label
that moves with the backend, the Dafny version, or the machine is a benchmark
result, not a label, and it is noise for both testing and training. Behaviour is
the part that *is* implementation-independent to check.

### Proofs written before the switch

The 33 files in `solutions-proved/` predate this model. Several charge `|s|` for
a `seq` update where the axioms now charge `1`. Those bounds are still **sound**
— they charge more than required — but they are no longer tight, and a couple
prove a quadratic where the axioms permit a linear. Do not treat an old proof's
bound as evidence about the label's tightness without re-reading its charges.

## 2. The proof technique

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

Dafny has no `log`. `solutions-proved/nlogn/` proves the true O(n log n) for merge sort
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

---

# Appendix: what the Python backend actually does

Everything below is **measurement, not charge.** It is kept because it is true
of the artifact, because it is the evidence that made the axioms necessary, and
because two rows in `solutions/` depend on it. None of it makes a row's label
wrong and none of it is a reason to rewrite a row.

Dafny 4.11.0's Python backend, min of 3 runs, interpreter startup subtracted.

## Where the divergence bites hardest

| operation | charged | backend | 
|---|---|---|
| `s[i := v]` | `1` | O(\|s\|) — full copy |
| `m[k := v]` | `1` | O(\|m\|) — `dict(self)` |
| `s + {x}` | `1` | O(\|s\|) — full copy |
| `m := m[k := v]` on a multiset | `1` | O(\|m\|) — `Counter(self)` |
| `s[a..b]` | `1` | O(1) — agrees |
| `s + [x]` | `1` | O(1) until something reads the accumulator |

## The two rows where this is load-bearing

`solutions/` is `seq`-only except twice, and both exceptions are measured, not
assumed:

| row | table | why `seq` cannot run it |
|---|---|---|
| `2826_42` | 1_000_004 entries | fills 1_000_002 of them in a loop reading earlier ones — ~10^12 element copies. 16s as an array; over a 60s per-test budget on the first test as a sequence. |
| `2128_34` | `r + 1`, `r` up to 30000 in its own tests | nested loop writes O(r) times per element — ~10^9 copies per test, across 88 tests. Seconds as an array; no test finished in four minutes as a sequence. |

Appending instead of updating rescues neither: `Seq.__add__` builds an O(1)
`Concat` rope, but the next indexed read forces it flat, so append/read
alternation is quadratic too. Under the axioms each row's `seq` and `array`
forms are charged identically; what the axioms cannot do is make the `seq` form
finish, and the gates are non-negotiable.

## The measurements

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

So a loop CPython runs in O(n) runs in O(n²) once translated with a seq update
and then executed by this backend.

Under the axioms this changes nothing about a row's class: `s[i := v]` is
charged `1`. It was once the largest defect class in the project — 93 rows —
and that class is closed.

### Slicing is a view, in a loop as well as a recursion

The table's "recursion on `s[1..]`" row was measured for the recursive shape
only, and two rows turned on whether a **loop** that peels slices costs the
same. It does. Peeling n elements one at a time, against a control doing the
same iterations with index arithmetic and no slicing:

    n        a := a[1..]   both ends   index control   recursion on s[1..]
    2000        5.3ms        5.6ms         0.8ms            8.8ms
    4000       10.5ms       12.0ms         1.7ms           17.3ms
    8000       20.5ms       28.3ms         3.3ms           32.8ms
    16000      41.3ms       44.7ms         6.4ms           65.6ms

All four double with n. Slicing a `seq` is a view, not a copy -- it costs a
constant, about 6x the bare index scan, and does not scale with `|s|`.

**This is where the Dafny is faster than CPython.** Python's `a = a[1:]` copies,
so the same loop is O(n**2) there. A row whose Python peels a list or string in
a loop is genuinely quadratic while its faithful-looking translation is linear:
that is an algorithm-level divergence, not a speedup. `2087_50` is the case.

What a slice does not excuse is concatenating the result back: `f(s[1..]) + [x]`
at every level is quadratic because of the concat, which is why `888_6` is
O(n**2) despite the slice being free.

### A multiset is linear, unlike the other two

`_dafny.MultiSet` subclasses `collections.Counter`, so `multiset(s)` is `Counter(s)`
and costs one pass. **Building** one is linear, not quadratic:

    n= 1000  0.28ms    n= 4000  0.96ms    n=16000  3.68ms
    n= 2000  0.45ms    n= 8000  1.80ms

Equality is linear too. Rebuilding both sides and comparing, n times over, scales
x4 per doubling -- 477ms / 1878 / 7452 / 29848 / 118190 at n = 1000..16000 -- which
is n comparisons each costing O(n), so one `multiset(a) == multiset(b)` is O(n).

So `multiset(a) == multiset(b)` is a **linear** permutation test, and a row whose
Python reaches the same answer with `sorted(a) == sorted(b)` is O(n log n). That
difference is an algorithm replacement, not a data-structure choice: see
`solutions-disputed/README.md` on the too-fast direction.

**Updating one is not.** `m := m[k := v]` on a multiset compiles to
`MultiSet.set`, which is `Counter(self)` -- the same full copy as `Map.set` and
`Seq.set`. In a loop it is quadratic, measured:

    n= 1000   34.2ms    n= 4000   500.8ms
    n= 2000  128.5ms    n= 8000  1951.2ms   -- x3.9 per doubling

So the split is per-operation, not per-type: bulk construction and comparison
are linear, element-at-a-time update copies. An earlier version of this section
said multiset "does not copy like set and map do", which was drawn from the
construction measurement and is false for updates.

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

For reference on the same machine, a `seq<int>` of n elements fills by index in
0.3 / 0.5 / 1.0ms — linear, and about 160x faster than the map build at n=4000.
A row that needs a keyed structure it writes to in a loop wants a `seq<T>`
indexed by a dense integer key, or a sorted `seq` with binary search, not a
`map`.

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

Refusing to charge `Join` looked conservative. It blocked 164 rows, sent four
agent runs to a decline they did not need, and manufactured an obstruction that
was never there. The two rules it bought are at the end of this file.

---

# How to measure, if you add an entry

Two rules, both bought with a real error recorded above.

- **Measure against a control, not against 2.0.** An exponent read off raw
  ratios in a noisy harness is not a measurement. Nothing here should be called
  superlinear again without a known-linear baseline beside it in the same table.
- **Overcharging is not the safe direction.** An undercharged operation turns a
  real O(n²) into a proved "O(n)" and Dafny still says verified; an overcharged
  one puts a correct label out of reach and invents a disagreement that is not
  there. Both were live in this file: the `Join` row is the first hazard, the
  old unconditional `|s|` append charge was the second.

