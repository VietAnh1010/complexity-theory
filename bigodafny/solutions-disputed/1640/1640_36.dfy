// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny sorts with `Sort` in O(n log n) and then calls `Gcd(lis[0]
//     - lis[i], g)` per element, each O(log) in the values, giving O(n log
//     n + n log max a_i); the Python's `math.gcd` loop matches.
//
//   how this label could be wrong, and what to check:
//     The label counts the sort but charges each gcd 1. Check the loop
//     calling `Gcd(lis[0] - lis[i], g)` n times: each call costs Euclid's
//     depth in the values. The Python's `math.gcd` pays the same, so the
//     label omits a value term.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 51, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Gcd", "IntToString"], "loop_depth":
//     1, "loops": 2, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["Sort"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 1216_D. Swords  (problem 1640, solution 1640_36)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n  = int(input())
// lis = sorted(map(int,input().split()),reverse = True)
// gg = 0
// aa=1
// ans=0
// for i in range(n):
//     gg = math.gcd(lis[0]-lis[i],gg)
// for i in range(n):
//     ans+=((lis[0]-lis[i])//gg)
// print(ans,gg)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma GcdPos(a: int, b: int)
  requires a >= 0 && b >= 0
  requires a > 0 || b > 0
  ensures Gcd(a, b) > 0
  decreases b
{
  if b > 0 {
    GcdPos(b, a % b);
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires exists j, k :: 0 <= j < |a_list| && 0 <= k < |a_list| && a_list[j] != a_list[k]
{
  var lis := Sort(a_list, (x: int, y: int) => x > y);
  assert StrictTotalOrder<int>((x: int, y: int) => x > y);
  SortIsSorted(a_list, (x: int, y: int) => x > y);
  SortKeepsElems(a_list, (x: int, y: int) => x > y);
  assert forall k :: 0 <= k < |lis| ==> lis[k] <= lis[0] by {
    forall k | 0 < k < |lis| ensures lis[k] <= lis[0] {
      assert !((x: int, y: int) => x > y)(lis[k], lis[0]);
    }
  }
  ghost var j, k :| 0 <= j < |a_list| && 0 <= k < |a_list| && a_list[j] != a_list[k];
  assert a_list[j] in lis && a_list[k] in lis;
  var g := 0;
  var i := 0;
  while i < |lis|
    invariant 0 <= i <= |lis|
    invariant g >= 0
    invariant g == 0 ==> forall q :: 0 <= q < i ==> lis[q] == lis[0]
    decreases |lis| - i
  {
    if g > 0 || lis[0] - lis[i] > 0 {
      GcdPos(lis[0] - lis[i], g);
    }
    g := Gcd(lis[0] - lis[i], g);
    i := i + 1;
  }
  assert g > 0;
  var ans := 0;
  i := 0;
  while i < |lis|
    decreases |lis| - i
  {
    ans := ans + (lis[0] - lis[i]) / g;
    i := i + 1;
  }
  output := IntToString(ans) + " " + IntToString(g);
}
