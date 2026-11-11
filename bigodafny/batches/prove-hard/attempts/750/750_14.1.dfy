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

include "../../../../prelude.dfy"

method Solve(n: int, data_points: seq<(int, int)>)
    returns (output: string, ghost steps: nat)
    ensures steps <= 4 * NLogN(|data_points|) + 44 * |data_points| + 10 + |output|
{
  steps := 0;
  steps := steps + (1 + 6 * |data_points|);
  var aArr := seq(|data_points|, i requires 0 <= i < |data_points| => data_points[i].0 + data_points[i].1);
  steps := steps + (1 + 6 * |data_points|);
  var bArr := seq(|data_points|, i requires 0 <= i < |data_points| => data_points[i].0 - data_points[i].1);
  steps := steps + SortCost(|aArr|);
  var aSorted := SortInts(aArr);
  steps := steps + SortCost(|bArr|);
  var bSorted := SortInts(bArr);
  SortCostWithin(|aArr|, |data_points|);
  SortCostWithin(|bArr|, |data_points|);
  ghost var base := steps;
  var res := 0;
  var i := 0;
  while i < |aSorted|
    invariant i <= |aSorted| && |aSorted| == |data_points|
    invariant steps <= base + 16 * i
    decreases |aSorted| - i
  {
    steps := steps + 3;
    ghost var i0 := i;
    ghost var s1 := steps;
    var cnt := 1;
    while i + 1 < |aSorted| && aSorted[i] == aSorted[i + 1]
      invariant i0 <= i < |aSorted|
      invariant steps <= s1 + 11 * (i - i0)
      decreases |aSorted| - i
    {
      steps := steps + (5 + if i + 1 < |aSorted| then 4 else 0);
      steps := steps + 1;
      cnt := cnt + 1;
      steps := steps + 1;
      i := i + 1;
    }
    steps := steps + (4 + if i + 1 < |aSorted| then 4 else 0);
    steps := steps + 4;
    res := res + cnt * (cnt - 1) / 2;
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 2;
  ghost var base2 := steps;
  i := 0;
  while i < |bSorted|
    invariant i <= |bSorted| && |bSorted| == |data_points|
    invariant steps <= base2 + 16 * i
    decreases |bSorted| - i
  {
    steps := steps + 3;
    ghost var i0 := i;
    ghost var s1 := steps;
    var cnt := 1;
    while i + 1 < |bSorted| && bSorted[i] == bSorted[i + 1]
      invariant i0 <= i < |bSorted|
      invariant steps <= s1 + 11 * (i - i0)
      decreases |bSorted| - i
    {
      steps := steps + (5 + if i + 1 < |bSorted| then 4 else 0);
      steps := steps + 1;
      cnt := cnt + 1;
      steps := steps + 1;
      i := i + 1;
    }
    steps := steps + (4 + if i + 1 < |bSorted| then 4 else 0);
    steps := steps + 4;
    res := res + cnt * (cnt - 1) / 2;
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 2;
  steps := steps + Digits(res);
  output := IntToString(res);
  IntToStringDigits(res);
}

import opened Prelude
