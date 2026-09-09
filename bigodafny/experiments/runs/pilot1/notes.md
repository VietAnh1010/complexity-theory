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
