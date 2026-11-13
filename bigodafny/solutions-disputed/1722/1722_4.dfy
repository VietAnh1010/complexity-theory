// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     `Gen1722_4` recurses once per unused cube j and per face of `a[j]`,
//     to depth n, so the call tree has on the order of n! * 6**n nodes,
//     exponential in n; the Python's `gen` is the identical backtracking
//     search.
//
//   how this label could be wrong, and what to check:
//     The label is polynomial, but `gen` explores every ordered choice of
//     distinct cubes and a face of each, about n! * 6**n calls, each
//     looping over n cubes. Check the recursion in `Gen1722_4`: it
//     branches over every unused cube and every face; the statement caps n
//     at 3, which by the value rule does not make the cost constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 50, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 3, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": true}
// --------------------------------------------------------------------

// 887_B. Cubes for Masha  (problem 1722, solution 1722_4)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def gen(cur, used, x):
//     pos.add(cur)
//     if x == n:
//         return
//     for j in range(n):
//         if not used[j]:
//             for i in a[j]:
//                 if i != 0 or x != 0:
//                     used[j] = True
//                     gen(cur * 10 + i, used, x + 1)
//                     used[j] = False
// 
// 
// n = int(input())
// a = []
// for i in range(n):
//     a.append(list(map(int, input().split())))
// pos = set()
// gen(0, [False] * n, 0)
// x = 1
// while x in pos:
//     x += 1
// print(x - 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
  requires n >= 0 && |lists| == n
{
  var used := seq(n, (idx: int) => false);
  var pos := Gen1722_4(n, lists, 0, used, 0, {});
  var x := 1;
  while x in pos
    decreases set y | y in pos && y >= x
  {
    ghost var before := set y | y in pos && y >= x;
    x := x + 1;
    assert x - 1 in before && x - 1 !in (set y | y in pos && y >= x);
    assert (set y | y in pos && y >= x) < before;
  }
  output := IntToString(x - 1);
}

method Gen1722_4(n: int, a: seq<seq<int>>, cur: int, used: seq<bool>, x: int, posIn: set<int>) returns (posOut: set<int>)
  requires 0 <= x <= n && |used| == n && |a| == n
  decreases n - x
{
  var pos := posIn + {cur};
  if x == n {
    posOut := pos;
    return;
  }
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    decreases n - j
  {
    if !used[j] {
      var k := 0;
      while k < |a[j]|
        invariant 0 <= k <= |a[j]|
        decreases |a[j]| - k
      {
        var i := a[j][k];
        if i != 0 || x != 0 {
          var used2 := used[j := true];
          pos := Gen1722_4(n, a, cur * 10 + i, used2, x + 1, pos);
        }
        k := k + 1;
      }
    }
    j := j + 1;
  }
  posOut := pos;
}
