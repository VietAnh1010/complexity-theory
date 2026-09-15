// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn+mlogm)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-batch-01-sonnet
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     `Sort(b_list, ...)` costs O(m log m), but inside the while loop over
//     i, `l := l[i := kSorted[ptr]]` copies all n elements of l on every
//     triggered index and can trigger up to min(n,m) times, giving an
//     O(n*m)-order term that dominates the labelled O(nlogn+mlogm);
//     Python's own `k.pop(0)` inside the same conditional shifts up to m
//     elements per pop and likewise produces an O(n*m)-order worst case
//     the original label did not account for, so both sides exceed the
//     stated bound for the same underlying reason.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 28, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": ["Sort", "SortInts"], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 814_A. An abandoned sentiment from past  (problem 101, solution 101_10)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=map(int,input().split())
// l=list(map(int,input().split()))
// k=list(sorted(map(int,input().split()),reverse=True))
// for i in range(n):
//     if l[i]==0:
//         l[i]=k[0]
//         k.pop(0)
// if l==sorted(l):
//     print("No")
// else:
//     print("Yes")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  var kSorted := Sort(b_list, (x: int, y: int) => x > y);
  var l := a_list;
  var ptr := 0;
  var i := 0;
  while i < n && i < |l|
    invariant 0 <= i
    invariant |l| == |a_list|
    invariant 0 <= ptr
    decreases n - i
  {
    if l[i] == 0 {
      if ptr < |kSorted| {
        l := l[i := kSorted[ptr]];
        ptr := ptr + 1;
      }
    }
    i := i + 1;
  }
  if l == SortInts(l) {
    output := "No\n";
  } else {
    output := "Yes\n";
  }
}
