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

include "../../prelude.dfy"
import opened Prelude

ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
}

ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(m: nat, n: nat)
  requires m <= n
  ensures CeilLog2(m) <= CeilLog2(n)
  decreases n
{
  if n <= 1 { }
  else if m <= 1 { }
  else { CeilLog2Monotone((m + 1) / 2, (n + 1) / 2); }
}

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma MulDistrib(a: nat, b: nat, k: nat, L: nat)
  requires a + b == k
  ensures a * L + b * L == k * L
{ }

lemma SortCostNLogN(k: nat)
  ensures SortCost(k) <= 2 * k * (CeilLog2(k) + 1) + 1
  decreases k
{
  if k <= 1 { return; }
  var a := k / 2;
  var b := k - k / 2;
  var L := CeilLog2(k);
  assert a + b == k;
  assert b == (k + 1) / 2;
  assert a <= b;
  SortCostNLogN(a);
  SortCostNLogN(b);
  CeilLog2Monotone(a, b);
  assert L == 1 + CeilLog2(b);
  assert CeilLog2(a) + 1 <= L;
  assert CeilLog2(b) + 1 == L;
  MulMonoRight(2 * a, CeilLog2(a) + 1, L);
  MulMonoRight(2 * b, CeilLog2(b) + 1, L);
  assert SortCost(a) <= 2 * a * L + 1;
  assert SortCost(b) <= 2 * b * L + 1;
  MulDistrib(2 * a, 2 * b, 2 * k, L);
  assert 2 * a * L + 2 * b * L == 2 * k * L;
  assert SortCost(k) == SortCost(a) + SortCost(b) + k;
  assert SortCost(k) <= 2 * k * L + k + 2;
  assert 2 * k * (L + 1) == 2 * k * L + 2 * k;
  assert k + 2 <= 2 * k + 1;
}

method Solve(n: int, m: int, data_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |data_list| == n
  requires forall k :: 0 <= k < n ==> |data_list[k]| >= 2
  ensures steps <= 4 * n * (CeilLog2(n) + 1) + 10 * n + 10
{
  var r := m;
  var a: seq<(int,int)> := [];
  var b: seq<(int,int)> := [];
  var i := 0;
  steps := 1;
  while i < n
    invariant 0 <= i <= n
    invariant |a| + |b| == i
    invariant steps <= 1 + 2 * i
    decreases n - i
  {
    var row := data_list[i];
    if row[1] < 0 {
      b := b + [(row[0], row[1])];
    } else {
      a := a + [(row[0], row[1])];
    }
    i := i + 1;
    steps := steps + 2;
  }
  assert |a| + |b| == n;
  assert |a| <= n;
  assert |b| <= n;
  SortCostNLogN(|a|);
  SortCostNLogN(|b|);
  CeilLog2Monotone(|a|, n);
  CeilLog2Monotone(|b|, n);
  MulMonoRight(2 * |a|, CeilLog2(|a|) + 1, CeilLog2(n) + 1);
  MulMonoRight(2 * |b|, CeilLog2(|b|) + 1, CeilLog2(n) + 1);
  assert SortCost(|a|) <= 2 * |a| * (CeilLog2(n) + 1) + 1;
  assert SortCost(|b|) <= 2 * |b| * (CeilLog2(n) + 1) + 1;
  a := Sort(a, (x: (int,int), y: (int,int)) => x.0 < y.0);
  b := Sort(b, (x: (int,int), y: (int,int)) => x.0 + x.1 > y.0 + y.1);
  steps := steps + SortCost(|a|) + SortCost(|b|);
  MulDistrib(2 * |a|, 2 * |b|, 2 * n, CeilLog2(n) + 1);
  assert steps <= 1 + 2 * n + 2 * n * (CeilLog2(n) + 1) + 2;
  var z := 1;
  var stop := false;
  i := 0;
  ghost var baseA := steps;
  assert baseA <= 2 * n * (CeilLog2(n) + 1) + 2 * n + 3;
  while i < |a| && !stop
    invariant 0 <= i <= |a|
    invariant steps <= baseA + 2 * (i + 1)
    decreases !stop, |a| - i
  {
    if a[i].0 > r {
      z := 0;
      stop := true;
    } else {
      r := r + a[i].1;
      i := i + 1;
    }
    steps := steps + 2;
  }
  assert steps <= baseA + 2 * (|a| + 1);
  assert steps <= 2 * n * (CeilLog2(n) + 1) + 2 * n + 3 + 2 * n + 2;
  stop := false;
  i := 0;
  ghost var baseB := steps;
  assert baseB <= 2 * n * (CeilLog2(n) + 1) + 4 * n + 5;
  while i < |b| && !stop
    invariant 0 <= i <= |b|
    invariant steps <= baseB + 2 * (i + 1)
    decreases !stop, |b| - i
  {
    if b[i].0 > r {
      z := 0;
      stop := true;
    } else {
      r := r + b[i].1;
      i := i + 1;
    }
    steps := steps + 2;
  }
  assert steps <= baseB + 2 * (|b| + 1);
  assert steps <= 2 * n * (CeilLog2(n) + 1) + 4 * n + 5 + 2 * n + 2;
  if z == 0 || r < 0 {
    output := "NO";
  } else {
    output := "YES";
  }
  steps := steps + 1;
  assert steps <= 2 * n * (CeilLog2(n) + 1) + 6 * n + 8;
}
