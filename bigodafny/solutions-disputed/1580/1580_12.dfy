// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The first loop in Solve (while val < a * c, appending to res and
//     stepping val by b) runs about a*c/b iterations, a cost in input
//     values, followed by an O(log) binary search over res; the Python
//     pays the same, so the label's n+m does not describe it.
//
//   how this label could be wrong, and what to check:
//     The label assumes the cost grows with two input sizes n and m, but
//     the inputs are three integers a, b, c with no collections. Open
//     Solve and check the first while loop: its bound is val < a * c with
//     val stepping by b, so it runs about a*c/b times; confirm the
//     Python's `while(val<a*c)` loop is identical. If the dataset maps n
//     and m onto values that make a*c/b equal n+m, the label could stand.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 35, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 195_A. Let's Watch Football  (problem 1580, solution 1580_12)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b,c=map(int,input().split())
// val=b
// res=[val]
// i=2
// while(val<a*c):
//     val=b*i
//     res+=[val]
//     i+=1
// n=len(res)
// l=0
// h=n-1
// ans=-1
// #print(res)
// while(l<=h):
//     mid=l+(h-l)//2
//     if(res[mid]+b*(c-1)<a*c):
//         ans=mid
//         l=mid+1
//     else:
//         h=mid-1
//     #print(mid)
// print(ans+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
  requires b >= 1
{
  var res: seq<int> := [b];
  var val := b;
  var it := 2;
  while val < a * c
    invariant it >= 2
    invariant val == b * (it - 1)
    decreases a * c - val
  {
    val := b * it;
    res := res + [val];
    it := it + 1;
  }
  var l := 0;
  var h := |res| - 1;
  var ans := -1;
  while l <= h
    invariant 0 <= l
    invariant h <= |res| - 1
    decreases h - l
  {
    var mid := l + (h - l) / 2;
    if res[mid] + b * (c - 1) < a * c {
      ans := mid;
      l := mid + 1;
    } else {
      h := mid - 1;
    }
  }
  output := IntToString(ans + 1);
}
