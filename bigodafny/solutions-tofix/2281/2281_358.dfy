// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+mlogm)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-17
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both Solve and the Python for-i-in-range(n) loop are a single linear
//     pass over a_list/a with O(1) work per element (a1/b/c updates, no
//     sort, no second collection), so the true cost is O(n) with no m
//     dimension present at all.
//
//   how this label could be wrong, and what to check:
//     The label names a second size dimension m and a log factor, but the
//     signature only takes n and a_list (a single seq_args=1). Check the
//     Python: there is no second input array, no .sort() call (a.sort() is
//     commented out), and power()/math are defined but never invoked, so
//     nothing produces an mlogm term.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 40, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 349_A. Cinema Line  (problem 2281, solution 2281_358)
// time complexity: O(n+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// mod=1000000007
// def power(a,b):
//     res=1
//     b=b%(mod-1)
//     while(b>0):
//         if b%2!=0:
//             res=((res%mod)*(a%mod))%mod
//         b=b//2
//         a=a%mod
//         a=(a*a)%mod
//     res=res%mod
//     return res
// #n=int(input())
// #a=[int(i) for i in input().split()]
// #c=[[0 for x in range(1001)] for y in range(1001)]
// #n,q=[int(i) for i in input().split()]
// #a.sort(reverse=True)
// n=int(input())
// a=[int(i) for i in input().split()]
// a1=0
// b=0
// c=0
// f=1
// for i in range(n):
//     if a[i]==50:
//         if a1>0:
//             a1-=1
//             b+=1
//         else:
//             f=0
//             break
//     elif a[i]==100:
//         if a1>0 and b>0:
//             a1-=1
//             b-=1
//             c+=1
//         elif a1>=3:
//             a1-=3
//             c+=1
//         else:
//             f=0
//             break
//     else:
//         a1+=1
// if f==0:
//     print("NO")
// else:
//     print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n <= |a_list|
{
  var a1 := 0;
  var b := 0;
  var c := 0;
  var f := true;
  var i := 0;
  while i < n && f
    invariant 0 <= i
    decreases n - i
  {
    var v := a_list[i];
    if v == 50 {
      if a1 > 0 {
        a1 := a1 - 1;
        b := b + 1;
      } else {
        f := false;
      }
    } else if v == 100 {
      if a1 > 0 && b > 0 {
        a1 := a1 - 1;
        b := b - 1;
        c := c + 1;
      } else if a1 >= 3 {
        a1 := a1 - 3;
        c := c + 1;
      } else {
        f := false;
      }
    } else {
      a1 := a1 + 1;
    }
    i := i + 1;
  }
  output := if f then "YES" else "NO";
}
