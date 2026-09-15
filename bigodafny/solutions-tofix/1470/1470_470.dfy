// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-09
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny finds the first and last out-of-range elements with two
//     independent linear scans (idx1, idx2) and never sorts, while
//     Python's `ar=sorted(ar)` call used to check for any oversized
//     element costs O(n log n); dropping the sort leaves the Dafny at
//     O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes the Dafny needs Python's `sorted(ar)` check for
//     any oversized element. Confirm the Dafny has no call to
//     SortInts/Sort/SortStrings anywhere and that both while loops break
//     as soon as they find one out-of-range element; if so the sort's cost
//     never appears in the Dafny and the tight class is linear.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 30, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 999_A. Mishka and Contest  (problem 1470, solution 1470_470)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// arr=list(map(int, input().split(' ')))
// ar=list(map(int, input().split(' ')))
// t=0
// for i in range (arr[0]):
//     if ar[i]>arr[1]:
//         t=ar.index(ar[i])
//         break
// ar.reverse()
// z=0
// for each in ar:
//     if each>arr[1]:
//         z=ar.index(each)
//         break
// ar=sorted(ar)
// s=0
// for h in ar:
//     if h>arr[1]:
//         s=1
// if s==0:
//     print (arr[0])
// else:
//     print (z+t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == n
{
  var idx1 := -1;
  var i := 0;
  while i < n && idx1 == -1
    invariant 0 <= i <= n
    decreases n - i
  {
    if a_list[i] > k { idx1 := i; }
    i := i + 1;
  }
  if idx1 == -1 {
    output := IntToString(n);
  } else {
    var idx2 := n - 1;
    var found2 := false;
    var j := n - 1;
    while j >= 0 && !found2
      invariant -1 <= j <= n - 1
      decreases j + 1
    {
      if a_list[j] > k { idx2 := j; found2 := true; }
      j := j - 1;
    }
    output := IntToString(idx1 + (n - 1 - idx2));
  }
}
