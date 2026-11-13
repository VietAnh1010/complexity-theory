// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+mlogm)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both the Python's `for i in range(n)` and the Dafny's loop over
//     `a_list` count evens and odds in one pass, O(n); nothing sorts and
//     no second list is read.
//
//   how this label could be wrong, and what to check:
//     The label names a second size and a sort, but the Python is a single
//     parity-counting loop over one list with no sort. Check for any
//     `sort` or second input list; there is neither, so the class is O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 24, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 25_A. IQ test  (problem 1093, solution 1093_909)
// time complexity: O(n+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #t=int(input())
// #for i in range(t):
// #    n,r=map(int,input().split())
// #    a=list(map(int,input().split()))
// #    bomb=0
// #    a.sort()
// #    a=list(set(a))
// #    n=len(a)
// #    for i in range(n):
// #        if (a[i]>bomb*r):
// #            bomb+=1
// #    print(bomb-1)
// n=int(input())
// a=list(map(int,input().split()))
// leven,lodd,ceven,codd=0,0,0,0
// for i in range(n):
//     if a[i]%2==0:
//         ceven+=1
//         leven=i
//     else:
//         codd+=1
//         lodd=i
// if codd==1:
//     print(lodd+1)
// else:
//     print(leven+1)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var countEven := 0;
  var countOdd := 0;
  var idxEven := 0;
  var idxOdd := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    if a_list[i] % 2 == 0 {
      countEven := countEven + 1;
      idxEven := i;
    } else {
      countOdd := countOdd + 1;
      idxOdd := i;
    }
    i := i + 1;
  }
  var ans := if countEven == 1 then idxEven + 1 else idxOdd + 1;
  output := IntToString(ans);
}

