// --- Python ---------------------------------------------------------
// n,r=map(int,input().split())
// a=[]
// b=[]
// for _ in range(n):
//     c,d=map(int,input().split())
//     if d<0:
//         b.append([c,d])
//     else:
//         a.append([c,d])
// a.sort(key = lambda x: x[0])
// b.sort(key = lambda x: x[0]+x[1],reverse=True)
// z=1
// for i in a:
//     if i[0]>r:
//         z=0
//         break
//     r+=i[1]
// for i in b:
//     if i[0]>r:
//         z=0
//         break
//     r+=i[1]
// if z==0 or r<0:
//     print('NO')
// else:
//     print('YES')
// #print(a,b)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int, m: int, data_list: seq<seq<int>>)
    returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |data_list| == n
  requires forall k :: 0 <= k < n ==> |data_list[k]| >= 2
  ensures steps <= 4 * NLogN(n) + 23 * n + 40
{
  steps := 0;
  var r := m;
  var a: seq<(int, int)> := [];
  var b: seq<(int, int)> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |a| + |b| == i
    invariant steps <= 11 * i
    decreases n - i
  {
    steps := steps + 2;
    steps := steps + 1;
    var row := data_list[i];
    steps := steps + 2;
    if row[1] < 0 {
      steps := steps + (4 + |[(row[0], row[1])]|);
      b := b + [(row[0], row[1])];
    } else {
      steps := steps + (4 + |[(row[0], row[1])]|);
      a := a + [(row[0], row[1])];
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  SortCostWithin(|a|, n);
  SortCostWithin(|b|, n);
  steps := steps + SortCost(|a|);
  a := Sort(a, (x: (int, int), y: (int, int)) => x.0 < y.0);
  steps := steps + SortCost(|b|);
  b := Sort(b, (x: (int, int), y: (int, int)) => x.0 + x.1 > y.0 + y.1);
  var z := 1;
  var stop := false;
  i := 0;
  ghost var s0 := steps;
  while i < |a| && !stop
    invariant 0 <= i <= |a|
    invariant steps <= s0 + 12 * i + (if stop then 8 else 0)
    decreases !stop, |a| - i
  {
    steps := steps + (4 + if i < |a| then 1 else 0);
    steps := steps + 3;
    if a[i].0 > r {
      z := 0;
      stop := true;
    } else {
      steps := steps + 3;
      r := r + a[i].1;
      steps := steps + 1;
      i := i + 1;
    }
  }
  steps := steps + (3 + if i < |a| then 1 else 0);
  stop := false;
  i := 0;
  ghost var s1 := steps;
  while i < |b| && !stop
    invariant 0 <= i <= |b|
    invariant steps <= s1 + 12 * i + (if stop then 8 else 0)
    decreases !stop, |b| - i
  {
    steps := steps + (4 + if i < |b| then 1 else 0);
    steps := steps + 3;
    if b[i].0 > r {
      z := 0;
      stop := true;
    } else {
      steps := steps + 3;
      r := r + b[i].1;
      steps := steps + 1;
      i := i + 1;
    }
  }
  steps := steps + (3 + if i < |b| then 1 else 0);
  steps := steps + (2 + if z == 0 then 0 else 1);
  if z == 0 || r < 0 {
    output := "NO";
  } else {
    output := "YES";
  }
}

import opened Prelude
