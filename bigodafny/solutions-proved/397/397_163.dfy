// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python sorts the Counter's values to take the largest, O(n log
//     n) as labelled; the Dafny builds `count` and finds `maxCount` with a
//     linear scan, never sorting, so it is O(n) and the translation
//     dropped the sort.
//
//   how this label could be wrong, and what to check:
//     The label comes from the Python's `sorted(c.values(),
//     reverse=True)[0]`, a sort over the distinct counts. Check that the
//     Dafny replaces it with a linear max scan over `count[a_list[i]]`;
//     with no sort the Dafny is O(n), a class below the labelled program.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 73, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 5, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": true, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1144_D. Equalize Them All  (problem 397, solution 397_163)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import collections
// 
// def solve():
//     N=int(input())
//     A=list(map(int,input().split()))
//     c=collections.Counter(A)
//     max_count = sorted(c.values(), reverse=True)[0]
//     max_key = [k for k in c.keys() if c[k] == max_count][0]
//     pivot = A.index(max_key)
//     ans=[]
//     for i in range(pivot-1, -1, -1):
//         if A[i]<max_key:
//             ans.append([1,i+1,i+2])
//         else:
//             ans.append([2,i+1,i+2])
//     #print(max_key,pivot)
//     for i in range(pivot+1, N):
//         if A[i]==max_key:
//             continue
//         if A[i]<max_key:
//             ans.append([1,i+1,i])
//         else:
//             ans.append([2,i+1,i])
//     print(len(ans))
//     for a in ans:
//         print(' '.join(list(map(str,a))))
// 
// solve()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| >= 1
  ensures steps <= 50 * |a_list| + 20 + 4 * |output|
{
  steps := 1;
  var count: map<int, int> := map[];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant forall k :: 0 <= k < i ==> a_list[k] in count
    invariant steps == 1 + 10 * i
    decreases |a_list| - i
  {
    var v := a_list[i];
    if v in count { count := count[v := count[v] + 1]; } else { count := count[v := 1]; }
    i := i + 1;
    steps := steps + 10;
  }
  var maxCount := 0;
  i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant forall k :: 0 <= k < |a_list| ==> a_list[k] in count
    invariant steps == 1 + 10 * |a_list| + 10 * i
    decreases |a_list| - i
  {
    steps := steps + 10;
    var c := count[a_list[i]];
    if c > maxCount { maxCount := c; }
    i := i + 1;
  }
  var pivot := 0;
  var found := false;
  i := 0;
  while i < |a_list| && !found
    invariant 0 <= i
    invariant forall k :: 0 <= k < |a_list| ==> a_list[k] in count
    invariant 0 <= pivot < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps <= 1 + 20 * |a_list| + 10 * i
    decreases |a_list| - i
  {
    steps := steps + 10;
    if count[a_list[i]] == maxCount {
      pivot := i;
      found := true;
    }
    i := i + 1;
  }
  ghost var b3 := steps;
  var maxKey := a_list[pivot];
  var ans: seq<string> := [];
  var j := pivot - 1;
  while j >= 0
    invariant -1 <= j < pivot
    invariant steps <= b3 + 14 * (pivot - 1 - j) + 2 * SumLen(ans)
    decreases j + 1
  {
    ghost var ans0 := ans;
    if a_list[j] < maxKey {
      ans := ans + ["1 " + IntToString(j + 1) + " " + IntToString(j + 2)];
    } else {
      ans := ans + ["2 " + IntToString(j + 1) + " " + IntToString(j + 2)];
    }
    ghost var line := ans[|ans| - 1];
    assert ans == ans0 + [line];
    IntToStringDigits(j + 1); IntToStringDigits(j + 2);
    SumLenSnoc(ans0, line);
    steps := steps + 14 + 2 * |line|;
    j := j - 1;
  }
  j := pivot + 1;
  while j < |a_list|
    invariant pivot + 1 <= j <= |a_list|
    invariant steps <= b3 + 14 * pivot + 14 * (j - pivot - 1) + 2 * SumLen(ans)
    decreases |a_list| - j
  {
    ghost var ans0 := ans;
    if a_list[j] != maxKey {
      if a_list[j] < maxKey {
        ans := ans + ["1 " + IntToString(j + 1) + " " + IntToString(j)];
      } else {
        ans := ans + ["2 " + IntToString(j + 1) + " " + IntToString(j)];
      }
      ghost var line := ans[|ans| - 1];
      assert ans == ans0 + [line];
      IntToStringDigits(j + 1); IntToStringDigits(j);
      SumLenSnoc(ans0, line);
      steps := steps + 2 * |line|;
    }
    steps := steps + 14;
    j := j + 1;
  }
  var resultLines := [IntToString(|ans|)] + ans;
  output := Join(resultLines, "\n");
  IntToStringDigits(|ans|);
  assert resultLines[1..] == ans;
  JoinLen(resultLines, "\n");
  steps := steps + Digits(|ans|) + |ans| + SumLen(resultLines) + |resultLines|;
}
