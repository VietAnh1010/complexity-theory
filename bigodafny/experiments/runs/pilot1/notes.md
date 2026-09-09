# pilot1 incidents

- `2650_140` (labeled) was attempted three times. The first agent stalled on it
  (62 tool calls, no result.json); I reset the file and relaunched. The stalled
  agent then woke twice more and rewrote the file before I stopped it, so the
  file was reset a second time at 16:45. Attempts kept as `.attempt1.dfy` and
  `.attempt2.dfy` in the example directory. Its labeled-arm trajectory numbers
  are therefore not comparable with the rest and are marked in results.csv.

- `1243_0` was called a refutation independently by BOTH arms. The Python does
  `sorted(g1) != sorted(g2)`; the Dafny does `multiset(s1) != multiset(s2)`.
  Measured: Dafny's `multiset(seq)` in the Python backend is linear (doubling n
  doubles the time), unlike `set<T>` which quadruples. So the translation is a
  complexity class faster than the program it translates, and the row's
  `O(nlogn+mlogm)` label describes the Python only. 2 rows in `solutions/` use
  `multiset(`; 1 of them replaces a sort. Isolated, not systemic.

## Guide version boundary (cohort split)

`GUIDE.md` changed between waves. Runs are no longer under identical
instructions, and that must be stated whenever the two cohorts are pooled.

- **v1** — charged `s + [x]` a flat `|s|`. Every run graded before this note.
  Archived at `guide_archive/GUIDE.v1.md`.
- **v2** — charges append `1` unless the loop reads the accumulator, which is
  what the measurement says, and tells the agent that `Join` has no honest
  charge and to give up rather than invent one. Archived at
  `guide_archive/GUIDE.v2.md`; every run from `1180_626` onward.

The change was not optional: v1 taught a rule a measurement contradicts, and
7 of 32 graded runs produced a verdict that is not citable because of it. But
it is a change to the apparatus mid-run, so the honest reading is two cohorts,
not one sample of 37.

`1180_626` blind held a `gave_up` stub whose `guess_basis` reasoned explicitly
from v1's append rule ("lst and lines each grow via seq-append (cost = current
length)"). The stub is archived at
`guide_archive/1180_626.blind.stub.result.json` and cleared, so the row is
re-run from scratch under v2 rather than carrying a guess derived from a rule
that has since been withdrawn.

## 1180_626 pair (first v2 examples)

Both arms **declined**: they priced the two-pointer merge at O(n+m) and the
merge sort at O(m log m), then refused `Join(lines, "\n")` over one line per
letter rather than invent a charge, which is what v2 tells them to do. Neither
touched `task.dfy`; both wrote the reason.

Two independent agents, one of them blind, hitting by themselves the wall this
session found by measurement is the strongest evidence yet that `Join` is the
binding constraint and not an artifact of one person's approach.

The blind arm's guess was `O(n+mlogm)` against a label of `O(n+m)log(n+m)`.

It also found a gap nothing here had recorded: `dorms[d_left := ...]` is a seq
**functional update**, not an append, and the laziness table covers only
append. Its cost is unmeasured. The agent took a full-copy charge of `|dorms|`
per update as the defensible reading, which would force O(a^2) on its own --
so the guess may be wrong for a reason that has nothing to do with `Join`.
Measure `s[i := v]` before that is believed either way.

### The `unchecked` precondition is resolved, not assumed

`precheck.py` reports this row's

    forall k :: 0 <= k < b ==> d_list[k] >= 1 && d_list[k] <= PrefixSum1180(c_list, a)

as `unchecked`: the clause calls a ghost helper the translator cannot express.
`unchecked` is not a pass, so it was evaluated directly against every stored
input -- **109 of 109 hold**, across public, private and generated. The clause
says each letter names a room between 1 and the total room count.

It is a precondition of the ORIGINAL translation; neither agent added a
`requires` (`added_requires: []` in both arms).

## Guide v3: the seq functional update

`s := s[i := v]` copies the whole sequence, every time. Measured:

    s := s[i := v]   n=2k .070s  4k .144s  8k .471s  16k 1.735s   quadratic
    a[i] := v        n=2k .036s  4k .038s  8k .037s  16k .042s    flat

No laziness, and reading or not reading makes no difference -- the opposite of
append in both respects. The guide priced only append, so an agent meeting a
seq update had nothing to go on.

This confirms `1180_626` blind, which called a full-copy charge "the defensible
reading" and concluded it forces O(a^2) on its own. The measurement says it was
right, so that row's guess is refuted by the seq update independent of `Join`.
An agent reasoning correctly about an unmeasured primitive is worth more than
the guess it got wrong.

v3 is an ADDITION, not a withdrawal: v1's append rule told agents something
false, v3 tells them something they were not told at all. Both are apparatus
changes and both are recorded, but only the v1 change invalidates prior
reasoning.

Two of the three remaining rows -- `1039_15` and `3029_114` -- are dominated by
this pattern, which is why the rule went in before they ran rather than after.

## 1039_15 pair (v3): both arms proved a quadratic, and the label is not at fault

Both arms proved `O(n**2)` on a row labelled `O(nlogn)`, independently, and
both named the same cause: `firstPos[x := i]` / `lastPos[x := i]` are seq
functional updates inside per-element loops, each a full copy.

The blind arm wrote it plainly -- *"the Python solution is O(n log n) (array
assigns are O(1) there) ... a translation-induced regression, not a property of
the original algorithm"* -- having guessed `O(n**2)` before proving anything.
So the disagreement is with the TRANSLATION. BigOBench's label is right about
the program it was measured on.

The labeled arm applied the refutation rule correctly, which is the rule six of
eight earlier agents got wrong: it landed above the claim and set `proves`, not
`refutes`, because an upper bound cannot refute from below. v2's rewording of
that section is doing work.

### This row breaks the blind arm's scoring, and it is not the only one

The blind agent reads the Dafny; the label was measured on the Python. Where a
translation artifact moves the class, a correct reading is scored wrong.
**7 of 19 graded blind rows contain a class-changing construct, and 5 of those
are scored incorrect** -- three of them guessing `O(n**2)` against `O(nlogn)`,
the signature of exactly this defect.

`RESULTS.md` now splits guess accuracy by that flag: 42% where the translation
cannot have re-classed the row, 29% where it can. Reported, not corrected --
the pooled 37% is still the honest answer to "did it name the label"; it is the
wrong denominator for "can it read a program".

### Grader gap this row exposed

The proof's `ensures` uses a Dafny let-binding:

    ensures var n := ParseInt(n_str); steps <= 10*(n+1)*(n+1) + ...

`extract_ensures` looked for `ensures steps <=`, so it returned nothing and a
verified, correct proof scored `bound=None`, hence not proved. Now let-bindings
are inlined before classifying.

Fixing it surfaced a second, older bug: the extractor matched to end-of-LINE,
so a multi-line `ensures` was graded on its first line only. `2962_1209` has
been graded on a truncated bound in both arms this whole time. It classified
the same by luck -- its dominant term is on the first line. Whitespace is now
normalised and the whole clause read. Re-checked all 41 graded rows: exactly
one class changes, the one being fixed.

### The `unchecked` precondition is resolved

`n >= 0 && |nums| == n && forall k :: 1 <= nums[k] <= n`, reported `unchecked`
because the clause binds `var`s precheck cannot translate. Evaluated directly:
**81 of 81** stored inputs hold, all tiers. It is the original's precondition;
neither agent added one.
