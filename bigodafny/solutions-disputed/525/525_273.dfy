// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops once over the n points reading pi[0], pi[1], pprev[0],
//     pprev[1] with O(1) arithmetic; the Python's min/max over a
//     two-number list are constant, so the whole thing is O(n) with no
//     second dimension.
//
//   how this label could be wrong, and what to check:
//     The label assumes variable score-pair width m. Check the statement:
//     each line is exactly two integers a_i, b_i; Solve reads only p[0],
//     p[1] and the Python's min/max over pair[i] act on two elements.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 31, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1131_B. Draw!  (problem 525, solution 525_273)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// pair = [None] * n
// 
// count = 0
// add = 0
// 
// for i in range(n):
//     pair[i] = list(map(int,input().split()))
// 
// 
// if(min(pair[0]) != 0):
//     add += min(pair[0]) + 1
// else:
//     add += 1
// 
// #print(add)
// 
// count+= add
// 
// for i in range(1,n):
//     if(min(pair[i])  - max(pair[i-1]) < 0):
//         continue
//     add = max( min(pair[i])  - max(pair[i-1]) + 1  , 0 )
//     if(pair[i-1][0] == pair[i-1][1]):
//         add -= 1
//     #print('bc',add)
//     count += add
// 
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, points: seq<seq<int>>) returns (output: string)
  requires n >= 1
  requires |points| == n
  requires forall k :: 0 <= k < |points| ==> |points[k]| >= 2
{
  var p0 := points[0];
  var mn0 := if p0[0] < p0[1] then p0[0] else p0[1];
  var count := if mn0 != 0 then mn0 + 1 else 1;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    decreases n - i
  {
    var pi := points[i];
    var pprev := points[i-1];
    var mni := if pi[0] < pi[1] then pi[0] else pi[1];
    var mxprev := if pprev[0] > pprev[1] then pprev[0] else pprev[1];
    if mni - mxprev >= 0 {
      var a2 := mni - mxprev + 1;
      var a3 := if a2 > 0 then a2 else 0;
      if pprev[0] == pprev[1] {
        a3 := a3 - 1;
      }
      count := count + a3;
    }
    i := i + 1;
  }
  output := IntToString(count) + "\n";
}
