// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops once over `pairs`, computing the next visit as `v +
//     k * (a / k + 1)` in constant time, so it is O(n); the Python's
//     `math.ceil` division is the same constant-time step with no sort.
//
//   how this label could be wrong, and what to check:
//     The label implies a sort or a log factor, but neither program sorts:
//     each doctor's next date is a closed-form ceiling division. Check the
//     Python for any `sort`, heap or bisect; there is none, and the loop
//     over doctors is single, so the class is O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 25, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 879_A. Borya's Diagnosis  (problem 827, solution 827_40)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # n=int(input())
// # n,k=map(int,input().split())
// # arr=list(map(int,input().split()))
// #ls=list(map(int,input().split()))
// #for i in range(m):
// # for _ in range(int(input())):
// #from collections import Counter
// #from fractions import Fraction
// #s=iter(input())
// from collections import deque
// import math
// ls=[]
// for i in range(int(input())):
//     n,k=map(int,input().split())
//     ls.append((n,k))
// #ls.sort()
// t=ls[0][0]
// c=0
// for i in range(1,len(ls)):
//     var=ls[i][0]
//     if var<=t:
//         c=math.ceil((t-ls[i][0])/ls[i][1])
//         if (t-ls[i][0])%ls[i][1]==0:
//             c+=1
//         #print("c",c)
//         t=ls[i][0]+ls[i][1]*c
//     else:
//         t=ls[i][0]
// print(t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
  requires |pairs| >= 1
  requires forall k :: 0 <= k < |pairs| ==> pairs[k].1 >= 1
{
  var t := pairs[0].0;
  var idx := 1;
  while idx < |pairs|
    invariant 1 <= idx <= |pairs|
    decreases |pairs| - idx
  {
    var v := pairs[idx].0;
    var k := pairs[idx].1;
    if v <= t {
      var a := t - v;
      var c := a / k + 1;
      t := v + k * c;
    } else {
      t := v;
    }
    idx := idx + 1;
  }
  output := IntToString(t) + "\n";
}
