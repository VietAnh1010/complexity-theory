// 1144_D. Equalize Them All  (problem 397, solution 397_80)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// n=int(input())
// l=list(map(int,input().split()))
// c,f=Counter(l).most_common(1)[0]
// a=int(l.index(c))
// print(n-f)
// for i in range(a-1,-1,-1):
//     if l[i]!=c:
//         print(1 if l[i]<c else 2,i+1,i+2)
// for i in range(a+1,len(l)):
//     if l[i]!=c:
//         print(1 if l[i]<c else 2,i+1,i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| >= 1
  ensures steps <= 40 * |a_list| + 4 * |output| + 30
{
  steps := 1;
  var count: map<int, int> := map[];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant forall k :: 0 <= k < i ==> a_list[k] in count
    invariant steps <= 1 + 10 * i
    decreases |a_list| - i
  {
    var v := a_list[i];
    if v in count { count := count[v := count[v] + 1]; } else { count := count[v := 1]; }
    i := i + 1;
    steps := steps + 10;
  }
  var maxCount := 0;
  i := 0;
  ghost var s1 := steps;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant forall k :: 0 <= k < |a_list| ==> a_list[k] in count
    invariant steps <= s1 + 10 * i
    decreases |a_list| - i
  {
    var c := count[a_list[i]];
    if c > maxCount { maxCount := c; }
    i := i + 1;
    steps := steps + 10;
  }
  var pivot := 0;
  var found := false;
  i := 0;
  ghost var s2 := steps;
  while i < |a_list| && !found
    invariant 0 <= i <= |a_list|
    invariant forall k :: 0 <= k < |a_list| ==> a_list[k] in count
    invariant 0 <= pivot < |a_list|
    invariant steps <= s2 + 10 * i
    decreases |a_list| - i
  {
    if count[a_list[i]] == maxCount {
      pivot := i;
      found := true;
    }
    i := i + 1;
    steps := steps + 10;
  }
  var maxKey := a_list[pivot];
  var lines: seq<string> := [IntToString(n - maxCount)];
  IntToStringDigits(n - maxCount);
  SumLenSnoc([], IntToString(n - maxCount));
  steps := steps + 5 + Digits(n - maxCount);
  ghost var L0 := SumLen(lines);
  ghost var s3 := steps;
  var j := pivot - 1;
  while j >= 0
    invariant -1 <= j < pivot
    invariant |lines| >= 1
    invariant steps + L0 <= s3 + 10 * (pivot - 1 - j) + SumLen(lines)
    decreases j + 1
  {
    if a_list[j] != maxKey {
      if a_list[j] < maxKey {
        ghost var line := "1 " + IntToString(j + 1) + " " + IntToString(j + 2);
        IntToStringDigits(j + 1); IntToStringDigits(j + 2);
        SumLenSnoc(lines, line);
        lines := lines + ["1 " + IntToString(j + 1) + " " + IntToString(j + 2)];
        steps := steps + |line|;
      } else {
        ghost var line := "2 " + IntToString(j + 1) + " " + IntToString(j + 2);
        IntToStringDigits(j + 1); IntToStringDigits(j + 2);
        SumLenSnoc(lines, line);
        lines := lines + ["2 " + IntToString(j + 1) + " " + IntToString(j + 2)];
        steps := steps + |line|;
      }
    }
    j := j - 1;
    steps := steps + 10;
  }
  j := pivot + 1;
  while j < |a_list|
    invariant pivot + 1 <= j <= |a_list|
    invariant |lines| >= 1
    invariant steps + L0 <= s3 + 10 * pivot + 10 * (j - pivot - 1) + SumLen(lines)
    decreases |a_list| - j
  {
    if a_list[j] != maxKey {
      if a_list[j] < maxKey {
        ghost var line := "1 " + IntToString(j + 1) + " " + IntToString(j);
        IntToStringDigits(j + 1); IntToStringDigits(j);
        SumLenSnoc(lines, line);
        lines := lines + ["1 " + IntToString(j + 1) + " " + IntToString(j)];
        steps := steps + |line|;
      } else {
        ghost var line := "2 " + IntToString(j + 1) + " " + IntToString(j);
        IntToStringDigits(j + 1); IntToStringDigits(j);
        SumLenSnoc(lines, line);
        lines := lines + ["2 " + IntToString(j + 1) + " " + IntToString(j)];
        steps := steps + |line|;
      }
    }
    j := j + 1;
    steps := steps + 10;
  }
  JoinLen(lines, "\n");
  output := Join(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
}
