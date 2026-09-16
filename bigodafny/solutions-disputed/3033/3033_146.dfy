// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-23
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     Inside the first `while i < |a|` loop (2n iterations), `pos0 :=
//     pos0[v := i+1]`, `pos1 := pos1[v := i+1]`, and `seen := seen[v :=
//     true]` are functional seq updates costing O(n) each, giving O(n**2)
//     total, while Python's `b[a[i]].append(i+1)` on a list-of-lists is
//     O(1) amortized per call so the Python is O(n) as labelled.
//
//   how this label could be wrong, and what to check:
//     The label assumes `pos0`/`pos1`/`seen` updates are O(1) as Python
//     list writes are. Open the first `while i < |a|` loop and confirm the
//     updates are seq functional updates `pos0 := pos0[v := i+1]` rather
//     than array writes `a[i] := v`; if they are seq updates each costs
//     O(n) (full copy per the cost table) and the loop runs O(n) times,
//     giving O(n**2).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 43, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1130_B. Two Cakes  (problem 3033, solution 3033_146)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=[int(v) for v in input().split()]
// b=[[] for _ in range(n+1)]
// for i in range(2*n):
//     b[a[i]].append(i+1)
// f=b[1][0]+b[1][1]-2
// for j in range(1,n):
//     p=f+abs(b[j][0]-b[j+1][0])+abs(b[j][1]-b[j+1][1])
//     q=f+abs(b[j][0]-b[j+1][1])+abs(b[j][1]-b[j+1][0])
//     f=min(p,q)
// print(f)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges_list: seq<int>) returns (output: string)
{
  var a := edges_list;
  if n < 1 {
    output := "";
    return;
  }
  var pos0 := seq(n + 1, _ => 0);
  var pos1 := seq(n + 1, _ => 0);
  var seen := seq(n + 1, _ => false);
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |pos0| == n + 1 && |pos1| == n + 1 && |seen| == n + 1
    decreases |a| - i
  {
    var v := a[i];
    if 1 <= v <= n {
      if !seen[v] {
        pos0 := pos0[v := i + 1];
        seen := seen[v := true];
      } else {
        pos1 := pos1[v := i + 1];
      }
    }
    i := i + 1;
  }
  var f := pos0[1] + pos1[1] - 2;
  var j := 1;
  while j < n
    invariant 1 <= j <= n
    invariant |pos0| == n + 1 && |pos1| == n + 1
    decreases n - j
  {
    var p := f + AbsInt(pos0[j] - pos0[j + 1]) + AbsInt(pos1[j] - pos1[j + 1]);
    var q := f + AbsInt(pos0[j] - pos1[j + 1]) + AbsInt(pos1[j] - pos0[j + 1]);
    f := if p < q then p else q;
    j := j + 1;
  }
  output := IntToString(f);
}
