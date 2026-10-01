// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(nlogn+mlogm)
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-r3d-03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve calls Sort on rectangles and on checks and then runs one loop
//     over each, giving O(nlogn+mlogm); the Python sorts c and p the same
//     way, so the label omits the m list, a naming difference if n is the
//     total size.
//
//   how this label could be wrong, and what to check:
//     The label may use n for the combined size of both lists. Check
//     whether n and m are independent in the signature: Solve sorts
//     rectangles (n) and checks (m) separately, so the tight class is
//     O(nlogn+mlogm).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 31, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": ["Sort"], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 785_B. Anton and Classes  (problem 1177, solution 1177_9)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// c=[]
// for i in range(n):
//     c.append(list(map(int,input().split())))
// m=int(input())
// p=[]
// for i in range(m):
//     p.append(list(map(int,input().split())))
// c.sort()
// p.sort()
// ans=0
// for i in range(n):
//     ans=max(ans,p[-1][0]-c[i][1])
// for i in range(m):
//     ans=max(ans,c[-1][0]-p[i][1])
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rectangles: seq<(int, int)>, m: int, checks: seq<(int, int)>) returns (output: string)
  requires n == |rectangles|
  requires m == |checks|
  requires n >= 1
  requires m >= 1
{
  var c := Sort(rectangles, (p: (int,int), q: (int,int)) => p.0 < q.0 || (p.0 == q.0 && p.1 < q.1));
  var p := Sort(checks, (a: (int,int), b: (int,int)) => a.0 < b.0 || (a.0 == b.0 && a.1 < b.1));
  var ans := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var cand := p[m-1].0 - c[i].1;
    if cand > ans { ans := cand; }
    i := i + 1;
  }
  i := 0;
  while i < m
    invariant 0 <= i <= m
    decreases m - i
  {
    var cand := c[n-1].0 - p[i].1;
    if cand > ans { ans := cand; }
    i := i + 1;
  }
  output := IntToString(ans);
}
