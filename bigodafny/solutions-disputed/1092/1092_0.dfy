// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny does five fixed divide-and-mod steps per element of
//     `a_list`, O(n); the Python's inner `while k != 0` lowers k through
//     at most five prize indices, a constant, so it is O(n) too.
//
//   how this label could be wrong, and what to check:
//     The label's m can only be the prize list, which always has exactly
//     five costs (the Dafny requires `|b_list| == 5`). Check the input
//     format; with five prizes the Python's bisect-and-reduce loop runs at
//     most a constant number of times per bar, so the class is O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 30, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["SortInts"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 208_D. Prizes, Prizes, more Prizes  (problem 1092, solution 1092_0)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import bisect
// 
// n = int(input())
// a = [int(x) for x in input().split()]
// p = [int(x) for x in input().split()]
// b = [0, 0, 0, 0, 0]
// s = 0
// for i in a:
//     s += i
//     k = bisect.bisect_right(p, s)
//     while k != 0:
//         if (k == 5) or (p[k] > s):
//             k -= 1
//         b[k] += s // p[k]
//         s %= p[k]
//         k = bisect.bisect_right(p, s)
// print(' '.join(list(map(str, b))))
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
  requires |b_list| == 5
  requires forall k :: 0 <= k < |b_list| ==> b_list[k] >= 1
{
  var prizes := SortInts(b_list);
  SortIntsKeepsElems(b_list);
  assert forall x :: x in prizes ==> x >= 1;
  assert prizes[0] in prizes && prizes[1] in prizes && prizes[2] in prizes && prizes[3] in prizes && prizes[4] in prizes;
  var aC := 0;
  var bC := 0;
  var cC := 0;
  var dC := 0;
  var eC := 0;
  var s := 0;
  var idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    s := s + a_list[idx];
    if s >= prizes[4] { eC := eC + FloorDiv(s, prizes[4]); s := FloorMod(s, prizes[4]); }
    if s >= prizes[3] { dC := dC + FloorDiv(s, prizes[3]); s := FloorMod(s, prizes[3]); }
    if s >= prizes[2] { cC := cC + FloorDiv(s, prizes[2]); s := FloorMod(s, prizes[2]); }
    if s >= prizes[1] { bC := bC + FloorDiv(s, prizes[1]); s := FloorMod(s, prizes[1]); }
    if s >= prizes[0] { aC := aC + FloorDiv(s, prizes[0]); s := FloorMod(s, prizes[0]); }
    idx := idx + 1;
  }
  output := Join([IntToString(aC), IntToString(bC), IntToString(cC), IntToString(dC), IntToString(eC)], " ") + "\n" + IntToString(s);
}

