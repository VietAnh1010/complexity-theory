// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-13
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     In the `while a < m - 1` loop each iteration does minn := "9" +
//     minn, which costs O(|minn|) under the concat row, so m iterations
//     total O(m**2); the Python's str(9)+minn copies the same way, so the
//     O(n) label is wrong for both, while the maxx appends are O(1)
//     amortised.
//
//   how this label could be wrong, and what to check:
//     The label assumes both string builds are linear. The second loop
//     prepends with `minn := "9" + minn` (and IntToString(s2) + minn), and
//     the cost table charges s + t as O(|t|), so each iteration copies the
//     growing minn. Open the loop `while a < m - 1` and the Python line
//     `minn=str(9)+minn`; if the prepend is accepted as O(1) the label
//     stands.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 51, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 489_C. Given Length and Sum of Digits...  (problem 2282, solution 2282_437)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// m, s = [int(a) for a in input().split()]
// maxx=""
// minn=""
// s1 = s
// s2 = s-1
// if s==0 and m==1: print(0, 0)
// elif s>9*m or s<1: print (-1, -1)
// elif m==1: print(s, s)
// else:
// 	for a in range(m):
// 		if s1>9:
// 			maxx+=str(9)
// 			s1-=9
// 		elif s1==0:
// 			maxx+=str(0)
// 		else:
// 			maxx+=str(s1)
// 			s1=0
// 	for a in range(m-1):
// 		if s2>9:
// 			minn=str(9)+minn
// 			s2-=9
// 		elif s2==0:
// 			minn=str(0)+minn
// 		else:
// 			minn=str(s2)+minn
// 			s2=0
// 	minn=str(s2+1)+minn
// 	print(minn, maxx)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int) returns (output: string, ghost steps: nat)
  ensures n < 2 ==> steps <= 10 + 3 * |output|
  ensures n >= 2 ==> steps <= (if n >= 0 then n else 0) * ((if n >= 0 then n else 0) + 20) + 30 + 2 * |output|
{
  var m := n;
  var s := k;
  steps := 1;
  if s == 0 && m == 1 {
    output := "0 0";
    steps := steps + 4;
  } else if s > 9 * m || s < 1 {
    output := "-1 -1";
    steps := steps + 6;
  } else if m == 1 {
    IntToStringDigits(s);
    output := IntToString(s) + " " + IntToString(s);
    steps := steps + 6 + 2 * Digits(s) + 1;
  } else {
    var maxx := "";
    var s1 := s;
    var a := 0;
    steps := steps + 6;
    while a < m
      invariant 0 <= a <= m
      invariant |maxx| == a
      invariant 0 <= s1
      invariant steps == 7 + 8 * a
      decreases m - a
    {
      if s1 > 9 {
        maxx := maxx + "9";
        s1 := s1 - 9;
      } else if s1 == 0 {
        maxx := maxx + "0";
      } else {
        assert Digits(s1) == 1;
        IntToStringDigits(s1);
        maxx := maxx + IntToString(s1);
        s1 := 0;
      }
      a := a + 1;
      steps := steps + 8;
    }
    var minn := "";
    var s2 := s - 1;
    a := 0;
    ghost var K: nat := m + 10;
    ghost var s0 := steps;
    while a < m - 1
      invariant 0 <= a <= m - 1
      invariant |minn| == a
      invariant 0 <= s2
      invariant steps <= s0 + a * K
      decreases (m - 1) - a
    {
      if s2 > 9 {
        minn := "9" + minn;
        s2 := s2 - 9;
      } else if s2 == 0 {
        minn := "0" + minn;
      } else {
        assert Digits(s2) == 1;
        minn := IntToString(s2) + minn;
        s2 := 0;
      }
      CostMulDistrib(a, 1, a + 1, K);
      a := a + 1;
      steps := steps + (a - 1) + 9;
    }
    assert a * K <= m * K by { CostMulMonoLeft(a, m, K); }
    assert m * K == m * (m + 20) - 10 * m by { CostMulDistrib(m, 0, m, 0); }
    IntToStringDigits(s2 + 1);
    minn := IntToString(s2 + 1) + minn;
    output := minn + " " + maxx;
    steps := steps + |minn| + 1 + |maxx| + 5;
  }
}
