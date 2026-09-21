// 903_C. Boxes Packing  (problem 1857, solution 1857_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=sorted(list(map(int,input().split())))
// d={}
// for i in a:
//     if i not in d:
//         d[i]=1
//     else:
//         d[i]+=1
// print(max(d.values()))
//
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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 5 * |a_list| + 6
{
  var sorted := SortInts(a_list);
  SortCostNLogN(|a_list|);
  var maxCount := 0;
  var i := 0;
  steps := 1 + SortCost(|a_list|);
  ghost var base1 := steps;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant steps <= base1 + 5 * i
    decreases |sorted| - i
  {
    var j := i;
    ghost var base2 := steps;
    while j < |sorted| && sorted[j] == sorted[i]
      invariant i <= j <= |sorted|
      invariant steps <= base2 + 2 * (j - i)
      decreases |sorted| - j
    {
      j := j + 1;
      steps := steps + 2;
    }
    var cnt := j - i;
    if cnt > maxCount { maxCount := cnt; }
    i := j;
    steps := steps + 3;
  }
  output := IntToString(maxCount);
  steps := steps + 1;
}
