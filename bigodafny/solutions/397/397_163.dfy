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
  var ans: seq<string> := [];
  var j := pivot - 1;
  while j >= 0
    decreases j + 1
  {
    if a_list[j] < maxKey {
      ans := ans + ["1 " + IntToString(j + 1) + " " + IntToString(j + 2)];
    } else {
      ans := ans + ["2 " + IntToString(j + 1) + " " + IntToString(j + 2)];
    }
    j := j - 1;
  }
  j := pivot + 1;
  while j < |a_list|
    decreases |a_list| - j
  {
    if a_list[j] != maxKey {
      if a_list[j] < maxKey {
        ans := ans + ["1 " + IntToString(j + 1) + " " + IntToString(j)];
      } else {
        ans := ans + ["2 " + IntToString(j + 1) + " " + IntToString(j)];
      }
    }
    j := j + 1;
  }
  var resultLines := [IntToString(|ans|)] + ans;
  output := Join(resultLines, "\n");
}
