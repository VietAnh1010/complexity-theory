// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-15
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The first while loop performs p := p[i := mx - a[i]] once per
//     iteration over n indices, and seq update is O(|p|) per the cost
//     table, making that loop O(n**2); the Python instead writes p[i] = mx
//     - a[i] into a preallocated list, which is O(1) per write and O(n)
//     overall before its O(nlogn) sort.
//
//   how this label could be wrong, and what to check:
//     The label assumes p[i] assignment is O(1) as in Python's list. Open
//     the first while loop and confirm it does `p := p[i := mx - a[i]]`
//     inside a loop over n iterations; a Dafny seq update copies the whole
//     sequence per write, giving O(n**2) for that loop alone, which
//     dominates the later O(nlogn) SortInts call.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 29, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": ["SortInts"], "uses_map":
//     false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p03948 AtCoder Regular Contest 063 - An Invisible Hand  (problem 2051, solution 2051_80)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #!/usr/bin python3
// # -*- coding: utf-8 -*-
// 
// import bisect
// 
// n, t = map(int, input().split())
// a = list(map(int, input().split()))
// mx = 0
// p = [0] * n
// for i in range(n-1,-1,-1):
//     mx = max(mx, a[i])
//     p[i] = mx - a[i]
// p.sort()
// print(n-bisect.bisect_left(p, p[-1]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string)
  requires n >= 1
  requires n == |numbers|
{
  var a := numbers;
  var mx := 0;
  var p: seq<int> := seq(n, idx requires 0 <= idx < n => 0);
  var i := n - 1;
  while i >= 0
    invariant -1 <= i <= n - 1
    invariant |p| == n
    decreases i + 1
  {
    if a[i] > mx { mx := a[i]; }
    p := p[i := mx - a[i]];
    i := i - 1;
  }
  var sortedP := SortInts(p);
  var target := sortedP[|sortedP| - 1];
  var lo := 0;
  while lo < |sortedP| && sortedP[lo] < target
    decreases |sortedP| - lo
  {
    lo := lo + 1;
  }
  output := IntToString(n - lo);
}
