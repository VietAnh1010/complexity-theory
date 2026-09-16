# Axiomatize collection cost; then settle on one container

Two decisions, in order. The first changes what the cost model *is*. The second
is a cleanup that the first makes not just safe but mandatory — and it runs the
opposite way to what an earlier draft of this plan proposed.

## 1. The cost model becomes an axiom set, not a measurement

Until now every entry in `COMPLEXITY.md` was justified by reading
`DafnyRuntimePython/_dafny/__init__.py` and timing the emitted Python. That made
the model true of *this backend at this version* and nothing else. Three
consequences we actually hit:

- The model changed under us four times in one session (map, multiset, slicing,
  `Std.Strings.ToNat`), and each change invalidated verdicts already filed.
- A row's class depended on which backend you compiled it for. `m[k := v]` is a
  `dict(self)` copy in Python and something else in C# or Java.
- The labels come from BigOBench measuring **CPython**, so a model derived from
  Dafny's Python backend was comparing two unrelated implementations and calling
  the difference a translation defect.

**The replacement.** Charge each collection operation its standard asymptotic
cost, as a stipulated axiom, independent of any backend:

| operation | charged | note |
|---|---|---|
| `s[i]`, `\|s\|` | O(1) | |
| `s[i := v]` | O(1) | stipulated — matches CPython's `lst[i]=v` |
| `s + [x]` | O(1) amortised | |
| `s + t` | O(\|t\|) | |
| `s[a..b]` | O(1) | a view |
| `m[k]`, `k in m`, `m[k := v]`, `\|m\|` | O(1) | hash semantics, as CPython's `dict` |
| `m.Keys`, `m.Values`, `m.Items` | O(\|m\|) | materialises |
| `x in s`, `s + {x}` on `set<T>` | O(1) | as CPython's `set` |
| `\|s\|` on a set, iteration | O(\|s\|) | |
| `multiset(s)` | O(\|s\|) | |
| `multiset(a) == multiset(b)` | O(\|a\|+\|b\|) | |
| `a[i]`, `a[i] := v` on `array<T>` | O(1) | listed for completeness; § 2 removes `array<T>` from the corpus |

This is the cost model a complexity-theory reader expects, and it is the one
BigOBench's labels were measured against.

**What it costs us.** The axioms are now *false of the artifact we ship*. A row
charged O(n) can take O(n²) wall-clock under `dafny translate py`. That is
acceptable only if it is stated loudly and in one place, so:

- `COMPLEXITY.md` gains a section saying the charges are stipulated, that the
  Python backend does not honour them, and which operations diverge and by how
  much. Keep every measurement already recorded — demote it from "the rule" to
  "what this backend actually does", which is exactly the evidence step 2 needs.
- `CLAUDE.md`'s `set<T>` section stays factually true but stops being a reason
  to avoid `set<T>` for *labelling* reasons. It becomes a performance note.

**What it does to the 178 queued rows.** Re-file, do not re-audit from scratch.
Every row whose `cause` is `translation` *solely* because of a copying
collection becomes `ok` under the axioms — the label was right and so is the
translation. Machine-filterable: `cause == "translation"` and evidence citing a
seq/map/set/multiset write. Roughly 30–40 of the 58 `translation` rows, and most
of the 52 `translation_defect` flags. The `label` rows (112) are untouched: they
were never about backend cost.

**Do this first.** Re-filing before the rewrite avoids rewriting rows that the
axioms already make correct.

## 2. Then: remove `array<T>`; the corpus keeps `seq`

An earlier draft of this plan had § 2 the other way round: rewrite `seq` rows to
`array<T>` to close the gap between the charged cost and the wall clock. The
axioms make that backwards.

**Why it reverses.** The array campaign existed to buy one thing — a `seq`
update that costs O(1) when you run it, not just when you charge it. Axiom 1
grants that by stipulation. What the campaign would still buy is a corpus with
two containers that the cost model charges identically, differing only in how
the *current* Python backend happens to implement them. That is exactly the
implementation-dependence the axioms were adopted to remove. A dataset where
`1053_38` uses `array<int>` and `2465_212` uses `seq<int>` for the same job
teaches a reader that the choice matters. Under the axioms it does not.

**Three further costs the array direction carries:**

- `array<T>` is heap state. It drags `modifies`, `reads` and `fresh` clauses
  through every signature that touches it, and loop invariants stop being about
  values and start being about the heap. `solutions-proved/` pays that twice,
  because a ghost step counter and a heap frame have to be maintained together.
- `array<T>` needs its length up front, so a row that appends without a bound
  cannot use it. That is not a small exception — it means the rewrite could
  never be complete, and an incomplete rewrite is the two-container corpus
  above with extra steps.
- Every `prelude.dfy` lemma is stated over `seq`. An array rewrite either
  duplicates them or forces `a[..]` conversions at each call, and `a[..]` is a
  real copy, so the rewrite would reintroduce at the boundary the cost it was
  removing from the body.

**The direction, then: `seq` everywhere.** 16 rows in `solutions/` allocated an
array. Rewrite each to `seq`:

| array | seq |
|---|---|
| `var a := new int[n];` | `var a := seq(n, _ => 0);` |
| `var a := new int[n](f);` | `var a := seq(n, f);` |
| `a[i] := v` | `a := a[i := v]` |
| `a.Length` | `\|a\|` |
| `a[i]`, `a[lo..hi]`, `a[..]` | unchanged — same syntax, and `a[..]` becomes a no-op |
| `modifies a`, `fresh(a)` | deleted |

Reads, slices and the whole-array expression need no edit at all, which is most
of why this direction is cheap and the other was not.

**The one structural case.** `2826_81` declares `BisectLeft(arr: array<int>,
...)`, so the container is in a signature, not just a local. Its parameter type
changes to `seq<int>` and its callers pass the sequence directly; nothing else
in that row depends on the array being mutable.

**Two exceptions, both measured.** 14 of the 16 rows converted with the
mechanical swap above, re-verified and re-gated. Two keep their `array<T>`,
each with a header comment stating why:

| row | table size | why `seq` cannot run it |
|---|---|---|
| `2826_42` | 1_000_004 | fills 1_000_002 entries in a loop that reads earlier ones — ~10^12 element copies. 16s as an array; exceeded a 60s per-test budget on the first test as a sequence. |
| `2128_34` | `r + 1`, `r` up to 30000 in its own tests | nested loop writes O(r) times per `neg` element — ~10^9 copies per test, across 88 tests. Seconds as an array; no test finished in four minutes as a sequence. |

Appending instead of updating rescues neither. `Seq.__add__` builds an O(1)
`Concat` rope, but the next indexed read forces it flat, so an append/read
alternation is quadratic as well.

Under the axioms each row's `seq` and `array` versions are charged identically,
so these exceptions say nothing about the cost model. They say the axioms are
false of this backend, and in these two rows that falsehood decides whether the
row runs at all. `validate.py` and `difftest.py` are non-negotiable, so the
array stays. The honest reading: the corpus is `seq`-only except where the gap
between the stipulated model and the artifact is load-bearing, and it is
load-bearing exactly twice.

**Scope.** `solutions/` only, as with every other sweep — `solutions-disputed/`
rows have disputed labels and `solutions-unscreened/` rows are not part of the
clean corpus. Both get the same treatment when they rejoin `solutions/`, and
until then their arrays are a known, recorded exception rather than a second
convention.

**The gate is unchanged and non-negotiable.** `validate.py` for strict rows,
`difftest.py` for loose ones, and `bigodafny/CLAUDE.md` § "Translate the
algorithm, not just the behaviour" still forbids changing the algorithm.
Swapping `array` for `seq` is a data-structure change within a complexity class,
which that section explicitly permits. Restructuring the loop is not. Re-run
`dafny verify` on every rewritten row: dropping a `modifies` clause can leave an
invariant that no longer parses, and an invariant about `a[..]` over an array is
not the same assertion as one about `a` over a sequence.

## Order of work

1. Write the axiom set into `COMPLEXITY.md`; demote the measurements to a
   backend-divergence appendix.
   **Done** — `COMPLEXITY.md` now leads with the charges and carries every
   measurement in an appendix labelled *what the Python backend actually does*.
   `.claude/skills/bigodafny-prove/SKILL.md` follows it.
2. Rewrite the audit prompt's cost table to the axioms. Note in it that the
   table changed, so a later reader does not think earlier batches used it.
   **Done** — `batches/labelaudit/PROMPT.md` carries the new table, a dated
   banner, a § *What this rules out as a verdict*, and a schema example that no
   longer teaches the closed defect class.
3. Re-file the queued rows mechanically; report how many moved back to `ok`.
   **Not run.** It changes verdicts already queued for manual review, so it
   waits on that review. Expect 30–40 of the 58 `translation` rows to return.
4. Rewrite the `array` rows in `solutions/` to `seq`, gated as above.
   **Done** — 14 rewritten, re-verified and re-gated; `2826_42` and `2128_34`
   recorded as measured exceptions.

## What the corpus measures under the axioms — settled

Under the axioms every label is a claim about an idealised machine rather than
about anything runnable here, so `validate.py` and `difftest.py` check
*behaviour only* and nothing in the pipeline checks the complexity claim except
the hand-written proofs in `solutions-proved/`.

**That is the intended design, not a gap.** A complexity label that depends on
which backend compiled the row, on the Dafny version, or on the machine it ran
on is not a label — it is a benchmark result, and it makes the dataset
inconsistent with itself across rows translated at different times. Both uses we
have for this corpus want the idealised reading:

- **Testing.** A model asked for the complexity of a row should answer from the
  algorithm. Grading it against wall-clock behaviour of one Dafny backend would
  mark a correct answer wrong.
- **Training.** A label that moves when the runtime changes is noise in the
  target.

So `validate.py` checking behaviour and nothing else is correct: behaviour is
the part that *is* implementation-independent to check. The complexity claim is
checked by proof, in `solutions-proved/`, where it belongs — and growing that
tier is the way to increase how much of the corpus is machine-checked, not
adding a timing gate.
