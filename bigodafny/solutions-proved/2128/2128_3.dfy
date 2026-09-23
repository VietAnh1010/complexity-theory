// 1203_F1. Complete the Projects (easy version)  (problem 2128, solution 2128_3)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

// PROOF NOTE (relation: confirms).
// One O(n) partition pass, then a sort of each partition. Both partitions hold
// at most n elements, so the prelude's SortCostWithin folds each sort into
// NLogN(n) directly -- the step prove-sample-7's agent could not make Z3 take
// with the product form in scope. The two scans are O(n) with an early exit.

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, data_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |data_list| == n
  requires forall k :: 0 <= k < n ==> |data_list[k]| >= 2
  ensures steps <= 4 * NLogN(n) + 9 * n + 14
{
  steps := 1;
  var r := m;
  var a: seq<(int,int)> := [];
  var b: seq<(int,int)> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |a| + |b| == i
    invariant steps == 1 + 3 * i
    decreases n - i
  {
    var row := data_list[i];
    if row[1] < 0 {
      b := b + [(row[0], row[1])];
    } else {
      a := a + [(row[0], row[1])];
    }
    i := i + 1;
    steps := steps + 3;
  }
  // two sorts over the two partitions, each at most n elements
  steps := steps + SortCost(|a|) + SortCost(|b|);
  SortCostWithin(|a|, n);
  SortCostWithin(|b|, n);
  a := Sort(a, (x: (int,int), y: (int,int)) => x.0 < y.0);
  b := Sort(b, (x: (int,int), y: (int,int)) => x.0 + x.1 > y.0 + y.1);
  assert |a| + |b| == n;
  ghost var s1 := steps;
  var z := 1;
  var stop := false;
  i := 0;
  while i < |a| && !stop
    invariant 0 <= i <= |a|
    invariant steps <= s1 + 3 * i + (if stop then 3 else 0)
    decreases !stop, |a| - i
  {
    if a[i].0 > r {
      z := 0;
      stop := true;
    } else {
      r := r + a[i].1;
      i := i + 1;
    }
    steps := steps + 3;
  }
  assert steps <= s1 + 3 * |a| + 3;
  ghost var s2 := steps;
  stop := false;
  i := 0;
  while i < |b| && !stop
    invariant 0 <= i <= |b|
    invariant steps <= s2 + 3 * i + (if stop then 3 else 0)
    decreases !stop, |b| - i
  {
    if b[i].0 > r {
      z := 0;
      stop := true;
    } else {
      r := r + b[i].1;
      i := i + 1;
    }
    steps := steps + 3;
  }
  assert steps <= s2 + 3 * |b| + 3;
  if z == 0 || r < 0 {
    output := "NO";
  } else {
    output := "YES";
  }
  steps := steps + 2;
}
