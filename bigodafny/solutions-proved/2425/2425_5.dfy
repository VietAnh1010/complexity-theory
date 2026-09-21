// 608_A. Saitama Destroys Hotel  (problem 2425, solution 2425_5)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// k = []
// a, b = map(int, input().split(' '))
// for i in range(a):
//     x, y = map(int, input().split(' '))
//     k.append([x,y])
// k.append([0, -1])
// k.sort()
// k.reverse()
//
// curr = b
// t = 0
// for i in k:
//     d = curr - i[0]
//     curr = i[0]
//     t = max(i[1], t+d)
// print(t)
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

method Solve(n: int, k: int, pairs: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires n >= 0 && n == |pairs|
  ensures steps <= 2 * (n + 1) * (CeilLog2(n + 1) + 1) + 5 * (n + 1) + 5
{
  steps := 1;
  var arr := pairs + [(0, -1)];
  steps := steps + 1;
  var m := |arr|;
  SortCostNLogN(m);
  steps := steps + SortCost(m);
  var sortedDesc := Sort(arr, (x: (int, int), y: (int, int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  assert |sortedDesc| == m;

  var curr := k;
  var t := 0;
  var idx := 0;
  while idx < |sortedDesc|
    invariant 0 <= idx <= |sortedDesc|
    invariant steps <= 1 + 1 + SortCost(m) + 4 * idx
    decreases |sortedDesc| - idx
  {
    var xi := sortedDesc[idx].0;
    var yi := sortedDesc[idx].1;
    var d := curr - xi;
    curr := xi;
    var cand := t + d;
    t := if yi > cand then yi else cand;
    idx := idx + 1;
    steps := steps + 4;
  }
  output := IntToString(t);
  steps := steps + 1;
}
