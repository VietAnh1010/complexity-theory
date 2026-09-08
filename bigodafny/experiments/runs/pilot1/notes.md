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
