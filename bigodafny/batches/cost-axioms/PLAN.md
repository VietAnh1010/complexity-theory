# Axiomatize collection cost; prefer concrete structures where a row allows it

Two decisions, in order. The first changes what the cost model *is*. The second
is a rewrite campaign that the first makes safe to run.

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
| `a[i]`, `a[i] := v` on `array<T>` | O(1) | already true concretely |

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

## 2. Then: prefer `array<T>` where the row permits it

With the axioms in place this is no longer a correctness fix. It is closing the
gap between what we charge and what we run, which buys two real things: rows
whose wall-clock matches their label, and a corpus that a reader can profile
without being told to ignore the numbers.

**Which rows.** Start from the concrete evidence, not a sweep:

    grep -rlE '\w+ := \w+\[[^]]+ := ' solutions --include='*.dfy'

93 rows carried a seq update when last counted. Cross-reference
`data/call_depth.jsonl` — rows at depth 0–1 are self-contained and safe to
rewrite; deeper rows push the structure through helper signatures and cost more.

**The rewrite.** `var a := new T[n]; a[i] := v;` in place of
`s := s[i := v]`. Measured 560x faster at n = 32k, and it is what the Python
does. Return `a[..]` where a `seq` is needed at the boundary.

**Where it does not apply, and do not force it:**

- `array<T>` needs its length up front. A row that appends with no known bound
  keeps its `seq` — append is already O(1) amortised under both the axioms and
  the backend, so there is nothing to fix.
- A `map` keyed by something without a dense integer range. `2389_42` keys by
  `char`, so `|freq| <= 26` and the copy never bites; an array indexed by
  `c - 'a'` is a fair rewrite there, but a map keyed by arbitrary ints is not
  an array.
- Any row in `solutions-tofix/`. Its label is disputed; rewriting the body first
  means the reviewer is judging code that no longer matches the verdict header.
- Rows whose `seq` is provably fixed-width. `1830_0` holds 26 elements; the
  update is already constant.

**The gate is unchanged and non-negotiable.** `validate.py` for strict rows,
`difftest.py` for loose ones, and `bigodafny/CLAUDE.md` § "Translate the
algorithm, not just the behaviour" still forbids changing the algorithm. Swapping
`seq` for `array` is a data-structure change within a complexity class, which
that section explicitly permits. Restructuring the loop is not.

Re-run `proofs.py` and `verify_all.py` afterwards: `solutions-verified/` rows
cite `seq` lemmas from `prelude.dfy`, and an `array` rewrite invalidates them.

## Order of work

1. Write the axiom set into `COMPLEXITY.md`; demote the measurements to a
   backend-divergence appendix.
2. Rewrite the audit prompt's cost table to the axioms. Note in it that the
   table changed, so a later reader does not think earlier batches used it.
3. Re-file the queued rows mechanically; report how many moved back to `ok`.
4. Only then start the `array<T>` rewrite, smallest-depth rows first, gated as
   above.

## The question this plan does not answer

Under the axioms, what does the corpus still measure? Every row's label becomes
a claim about an idealised machine rather than about anything runnable here.
That is the normal situation in complexity theory and it is defensible — but it
means `validate.py` and `difftest.py` check *behaviour only*, and nothing in the
pipeline checks the complexity claim except the hand-written proofs in
`solutions-verified/`. Worth deciding whether that tier should grow.
