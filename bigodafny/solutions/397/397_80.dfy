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

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var count: map<int, int> := map[];
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var v := a_list[i];
    if v in count { count := count[v := count[v] + 1]; } else { count := count[v := 1]; }
    i := i + 1;
  }
  var maxCount := 0;
  i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var c := count[a_list[i]];
    if c > maxCount { maxCount := c; }
    i := i + 1;
  }
  var pivot := 0;
  var found := false;
  i := 0;
  while i < |a_list| && !found
    decreases |a_list| - i
  {
    if count[a_list[i]] == maxCount {
      pivot := i;
      found := true;
    }
    i := i + 1;
  }
  var maxKey := a_list[pivot];
  var lines: seq<string> := [IntToString(n - maxCount)];
  var j := pivot - 1;
  while j >= 0
    decreases j + 1
  {
    if a_list[j] != maxKey {
      if a_list[j] < maxKey {
        lines := lines + ["1 " + IntToString(j + 1) + " " + IntToString(j + 2)];
      } else {
        lines := lines + ["2 " + IntToString(j + 1) + " " + IntToString(j + 2)];
      }
    }
    j := j - 1;
  }
  j := pivot + 1;
  while j < |a_list|
    decreases |a_list| - j
  {
    if a_list[j] != maxKey {
      if a_list[j] < maxKey {
        lines := lines + ["1 " + IntToString(j + 1) + " " + IntToString(j)];
      } else {
        lines := lines + ["2 " + IntToString(j + 1) + " " + IntToString(j)];
      }
    }
    j := j + 1;
  }
  output := Join(lines, "\n");
}
