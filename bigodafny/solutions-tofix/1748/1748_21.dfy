// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-12
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     `SumSeq(d_list[i..])` is called once per outer iteration i=0..m-1,
//     each costing O(m-i); summed over the loop that is Theta(m**2), and
//     Python's `sum(c[i:])` recomputes the identical suffix the same way,
//     so the quadratic cost is inherent to both sources, not introduced by
//     translation.
//
//   how this label could be wrong, and what to check:
//     The label assumes the suffix total `sum(c[i:])` (Python) /
//     `SumSeq(d_list[i..])` (Dafny) is maintained incrementally in O(1)
//     per step of the outer `i`/`m` loop. Open both sources and check
//     whether that suffix sum is recomputed from scratch on every
//     iteration of the outer loop instead of updated by subtracting
//     `c[i-1]`; if it is recomputed, both sources pay Theta(m) per outer
//     step summing to Theta(m**2) (m<=n), so the O(n) label is wrong for
//     the Python too, not just the translation.
//
//   structural facts (deterministic, from labelaudit.py):
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
