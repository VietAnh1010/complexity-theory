// 621_B. Wet Shark and Bishops  (problem 750, solution 750_14)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// 
// n=int(sys.stdin.readline())
// a=[]
// b=[]
// res=0
// for i in range(n):
//     _a, _b = list(map(int, sys.stdin.readline().split()))
//     a.append(_a+_b)
//     b.append(_a-_b)
// 
// a.sort()
// b.sort()
// i=0
// while i<n:
//     cnt=1
//     while i+1<len(a) and a[i]==a[i+1]:
//         cnt+=1
//         i+=1
//     res+=cnt*(cnt-1)//2
//     i+=1
// 
// i=0
// while i<n:
//     cnt=1
//     while i+1<len(b) and b[i]==b[i+1]:
//         cnt+=1
//         i+=1
//     res+=cnt*(cnt-1)//2
//     i+=1
// 
// print(res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, data_points: seq<(int, int)>) returns (output: string)
{
  var aArr := seq(|data_points|, i requires 0 <= i < |data_points| => data_points[i].0 + data_points[i].1);
  var bArr := seq(|data_points|, i requires 0 <= i < |data_points| => data_points[i].0 - data_points[i].1);
  var aSorted := SortInts(aArr);
  var bSorted := SortInts(bArr);
  var res := 0;
  var i := 0;
  while i < |aSorted|
    decreases |aSorted| - i
  {
    var cnt := 1;
    while i+1 < |aSorted| && aSorted[i] == aSorted[i+1]
      decreases |aSorted| - i
    {
      cnt := cnt + 1;
      i := i + 1;
    }
    res := res + cnt*(cnt-1)/2;
    i := i + 1;
  }
  i := 0;
  while i < |bSorted|
    decreases |bSorted| - i
  {
    var cnt := 1;
    while i+1 < |bSorted| && bSorted[i] == bSorted[i+1]
      decreases |bSorted| - i
    {
      cnt := cnt + 1;
      i := i + 1;
    }
    res := res + cnt*(cnt-1)/2;
    i := i + 1;
  }
  output := IntToString(res);
}
