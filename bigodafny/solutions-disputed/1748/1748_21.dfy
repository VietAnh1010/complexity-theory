// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each of the m iterations calls SumSeq(d_list[i..]), which is O(m-i),
//     so that alone is O(m**2) while the zero and block padding loops
//     total O(n). The Python's sum(c[i:]) in the for loop has the same
//     quadratic cost, so the label O(n) is wrong for both.
//
//   how this label could be wrong, and what to check:
//     The label assumes the loop body is O(1) per platform. Check var
//     suffix := SumSeq(d_list[i..]) inside the while i < m loop: it is
//     linear in the remaining platforms, giving O(m**2) with m <= n
//     because every platform has length at least 1.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 48, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "SumSeq"],
//     "loop_depth": 2, "loops": 4, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1256_C. Platforms Jumping  (problem 1748, solution 1748_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m, d = list(map(int, input().strip().split(' ')))
// c = list(map(int, input().strip().split(' ')))
// 
// 
// res = []
// for i, ci in enumerate(c):
//     empty = n - len(res) - sum(c[i:])
//     if empty >= d - 1:
//         res.extend(['0']*(d - 1))
//     else:
//         res.extend(['0'] * empty)
//     res.extend([str(i + 1) for _ in range(ci)])
// 
// if n - len(res) < d:
//     res.extend(['0'] * (n - len(res)))
//     print("YES")
//     print(' '.join(res))
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
  // b is the number of blocks, one per entry of d_list
  requires b <= |d_list|
{
  var n := a;
  var m := b;
  var d := c;
  var res: seq<string> := [];
  var i := 0;
  while i < m
    invariant 0 <= i
    decreases m - i
  {
    var ci := d_list[i];
    var suffix := SumSeq(d_list[i..]);
    var empty := n - |res| - suffix;
    var zeros := if empty >= d - 1 then d - 1 else empty;
    var z := 0;
    while z < zeros
      decreases zeros - z
    {
      res := res + ["0"];
      z := z + 1;
    }
    var k := 0;
    while k < ci
      decreases ci - k
    {
      res := res + [IntToString(i + 1)];
      k := k + 1;
    }
    i := i + 1;
  }
  if n - |res| < d {
    var pad := n - |res|;
    var p := 0;
    while p < pad
      decreases pad - p
    {
      res := res + ["0"];
      p := p + 1;
    }
    output := "YES\n" + Join(res, " ");
  } else {
    output := "NO";
  }
}
