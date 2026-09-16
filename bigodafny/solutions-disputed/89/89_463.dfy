// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-01-sonnet
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each of the n loop iterations reads only the five fixed positions
//     k[0] through k[4] of the current row and never loops over the row's
//     own length, so row width m never enters the cost in either the Dafny
//     or the Python, which only ever indexes k[0], k[1], k[2], k[3] and
//     k[-1].
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 31, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1244_A. Pens and Pencils  (problem 89, solution 89_463)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for i in range(n):
//    k=list(map(int,input().split()))
//    if k[0]%k[2]==0:
//      x=k[0]//k[2]
//    else:
//      x=k[0]//k[2]+1
//    if k[1]%k[3]==0:
//      y=k[1]//k[3]
//    else:
//      y=k[1]//k[3]+1
//    if (x+y)<=k[-1]:
//      print(x,y)
//    else:
//      print('-1')
//    
// 
// 
// 
// 
// 
// 
// 
//       
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
  requires n >= 0
  requires |lists| == n
  requires forall idx :: 0 <= idx < |lists| ==>
    |lists[idx]| >= 5 && lists[idx][2] != 0 && lists[idx][3] != 0
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var k := lists[i];
    var k0 := k[0];
    var k1 := k[1];
    var k2 := k[2];
    var k3 := k[3];
    var k4 := k[4];
    var x := if k0 % k2 == 0 then k0 / k2 else k0 / k2 + 1;
    var y := if k1 % k3 == 0 then k1 / k3 else k1 / k3 + 1;
    if x + y <= k4 {
      parts := parts + [IntToString(x) + " " + IntToString(y)];
    } else {
      parts := parts + ["-1"];
    }
    i := i + 1;
  }
  output := Join(parts, "\n");
}
