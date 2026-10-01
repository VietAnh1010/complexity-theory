// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n+mlogm)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-u01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve sorts the m day values with SortInts, O(m log m), then makes
//     linear passes over the string length |s| (has[] fill, prefix sums,
//     copy, swap loop), so O(n+m log m) with n=|s|; the Python's
//     sorted(map(int, ...)) plus loops over n+3 does the same, so a single
//     nlogn label omits a size.
//
//   how this label could be wrong, and what to check:
//     The label O(nlogn) names one size, but the code pays for two
//     independent ones: the string length and the number of days. Find
//     `SortInts(a_list)` (sorts the m day values) and the loops over
//     `strLen` that fill, prefix-sum and swap over |s|. Confirm in the
//     statement that |s| (up to 2*10^5) and m (up to 10^5) are separate
//     inputs.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 90, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 5,
//     "recursive_helpers": 3, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": ["Merge", "Sort", "SortInts"], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 525_B. Pasha and String  (problem 380, solution 380_112)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = list(input())
// m = int(input())
// n=len(s)
// lis = sorted(map(int,input().split()))
// has=[0]*(n+3)
// for i in range(m):
//     a=lis[i]
//     has[a-1]+=1
// for i in range(1,n+2):
//     has[i]+=has[i-1]       
// for i in range(n//2):
//     if has[i]%2:
//         s[i],s[n-i-1]=s[n-i-1],s[i]
// print(''.join(s))               
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MergeElemsInt(a: seq<int>, b: seq<int>, less: (int, int) -> bool)
  ensures forall x :: x in Merge(a, b, less) ==> x in a || x in b
  decreases |a| + |b|
{
  if |a| == 0 {
  } else if |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeElemsInt(a, b[1..], less);
  } else {
    MergeElemsInt(a[1..], b, less);
  }
}

lemma SortElemsInt(s: seq<int>, less: (int, int) -> bool)
  ensures forall x :: x in Sort(s, less) ==> x in s
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortElemsInt(s[..|s| / 2], less);
    SortElemsInt(s[|s| / 2..], less);
    MergeElemsInt(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

lemma SortIntsElems(s: seq<int>)
  ensures forall x :: x in SortInts(s) ==> x in s
{
  SortElemsInt(s, (x, y) => x < y);
}

method Solve(s: string, n: int, a_list: seq<int>) returns (output: string)
  requires n >= 0
  requires |a_list| >= n
  requires forall v :: v in a_list ==> 1 <= v <= |s|
{
  var m := n;
  var strLen := |s|;
  var aSorted := SortInts(a_list);
  assert |aSorted| == |a_list|;
  SortIntsElems(a_list);
  assert forall v :: v in aSorted ==> 1 <= v <= |s|;
  var has := new int[strLen + 3];
  var k := 0;
  while k < strLen + 3
    decreases strLen + 3 - k
  {
    has[k] := 0;
    k := k + 1;
  }
  var i := 0;
  while i < m
    invariant 0 <= i
    invariant i <= m
    invariant m <= |aSorted|
    invariant forall v :: v in aSorted ==> 1 <= v <= |s|
    decreases m - i
  {
    var a := aSorted[i];
    assert a in aSorted;
    has[a - 1] := has[a - 1] + 1;
    i := i + 1;
  }
  i := 1;
  while i < strLen + 2
    decreases strLen + 2 - i
  {
    has[i] := has[i] + has[i - 1];
    i := i + 1;
  }
  var arr := new char[strLen];
  i := 0;
  while i < strLen
    decreases strLen - i
  {
    arr[i] := s[i];
    i := i + 1;
  }
  i := 0;
  while i < strLen / 2
    decreases strLen / 2 - i
  {
    if has[i] % 2 == 1 {
      var tmp := arr[i];
      arr[i] := arr[strLen - i - 1];
      arr[strLen - i - 1] := tmp;
    }
    i := i + 1;
  }
  output := arr[..];
}
