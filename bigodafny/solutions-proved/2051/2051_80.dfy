// p03948 AtCoder Regular Contest 063 - An Invisible Hand  (problem 2051, solution 2051_80)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #!/usr/bin python3
// # -*- coding: utf-8 -*-
//
// import bisect
//
// n, t = map(int, input().split())
// a = list(map(int, input().split()))
// mx = 0
// p = [0] * n
// for i in range(n-1,-1,-1):
//     mx = max(mx, a[i])
//     p[i] = mx - a[i]
// p.sort()
// print(n-bisect.bisect_left(p, p[-1]))
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

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1
  requires n == |numbers|
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 8 * n + 10
{
  var a := numbers;
  var mx := 0;
  var p: seq<int> := seq(n, idx requires 0 <= idx < n => 0);
  steps := 1 + n;
  var i := n - 1;
  while i >= 0
    invariant -1 <= i <= n - 1
    invariant |p| == n
    invariant steps <= 1 + n + 3 * (n - 1 - i)
    decreases i + 1
  {
    if a[i] > mx { mx := a[i]; }
    p := p[i := mx - a[i]];
    i := i - 1;
    steps := steps + 3;
  }
  SortCostNLogN(n);
  steps := steps + SortCost(n);
  var sortedP := SortInts(p);
  var target := sortedP[|sortedP| - 1];
  steps := steps + 2;
  var lo := 0;
  while lo < |sortedP| && sortedP[lo] < target
    invariant 0 <= lo <= |sortedP|
    invariant steps <= 1 + n + 3 * n + SortCost(n) + 2 + 3 * lo
    decreases |sortedP| - lo
  {
    lo := lo + 1;
    steps := steps + 3;
  }
  output := IntToString(n - lo);
  steps := steps + 1;
}
