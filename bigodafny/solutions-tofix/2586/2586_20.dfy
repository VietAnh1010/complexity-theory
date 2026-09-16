// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-batch-19
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     l2 := l2[idx := 1] and l2 := l2[j := 1] are seq updates on an array
//     of size n*(n+1)/2 which is O(n**2), and one such update happens per
//     outer iteration (n times), giving O(n**3) total write cost, while
//     Python's l2[idx]=1 is an O(1) list write so the Python stays O(n**2)
//     as labeled.
//
//   how this label could be wrong, and what to check:
//     The label assumes each badge-slot write is O(1) as in Python's
//     l2[idx]=1. Confirm size = n*(n+1)/2 makes l2 quadratic in n (facts
//     show n up to 3000), then check that l2 := l2[idx := 1] and l2 :=
//     l2[j := 1] are seq updates that copy the full size-length seq; since
//     one such update fires per outer iteration (n times), the true write
//     cost multiplies to cubic.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 37, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 546_B. Soldier and Badges  (problem 2586, solution 2586_20)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l1=list(map(int,input().split()))
// l2=[0]*int(n*(n+1)/2)
// cost=0
// for i in range (n):
//     if(l2[l1[i]-1]==0):
//         l2[l1[i]-1]=1
//     elif(l2[l1[i]-1]==1):
//         while(l2[l1[i]-1]==1):
//             cost+=1
//             l1[i]+=1
//         l2[l1[i]-1]=1
// print(cost)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
{
  var size := n * (n + 1) / 2;
  var l2 := seq(size, _ => 0);
  var cost := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |l2| == size
    decreases n - i
  {
    var idx := a_list[i] - 1;
    if 0 <= idx < size {
      if l2[idx] == 0 {
        l2 := l2[idx := 1];
      } else {
        var j := idx;
        while j < size && l2[j] == 1
          invariant idx <= j
          invariant |l2| == size
          decreases size - j
        {
          cost := cost + 1;
          j := j + 1;
        }
        if j < size {
          l2 := l2[j := 1];
        }
      }
    }
    i := i + 1;
  }
  output := IntToString(cost);
}
