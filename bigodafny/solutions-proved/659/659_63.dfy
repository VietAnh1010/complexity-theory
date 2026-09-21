// 127_B. Canvas Frames  (problem 659, solution 659_63)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int, input().split()))
// a.sort()
// b,t,c=[],1,0
// for i in range(n):
//     if i==n-1 or a[i]!=a[i+1]:
//         c+=t//4
//         if t%4>=2:b.append(t%2)
//         t=1
//     else:t+=1
// print(len(b)//2+c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound (see
// solutions-proved/nlogn/603/603_284.dfy for the same argument) ----------

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

method Solve(n: int, ratings: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |ratings| * (CeilLog2(|ratings|) + 1) + 5 * |ratings| + 5
{
  steps := 1;
  SortCostNLogN(|ratings|);
  steps := steps + SortCost(|ratings|);
  var a := SortInts(ratings);
  assert |a| == |ratings|;
  var bLen := 0;
  var t := 1;
  var c := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant steps <= 1 + SortCost(|ratings|) + 4 * i
    decreases |a| - i
  {
    if i == |a| - 1 || a[i] != a[i+1] {
      c := c + t / 4;
      if t % 4 >= 2 { bLen := bLen + 1; }
      t := 1;
    } else {
      t := t + 1;
    }
    i := i + 1;
    steps := steps + 4;
  }
  output := IntToString(bLen / 2 + c);
  steps := steps + 1;
}
