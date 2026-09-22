// 1130_B. Two Cakes  (problem 3033, solution 3033_135)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// class House:
//     c = 0
// 
//     def __init__(self, val):
//         self.id = House.c + 1
//         self.val = int(val)
//         House.c += 1
// 
// n = int(input())
// a = list(map(House, input().split()))
// a.sort(key=lambda x: x.val)
// length = 0
// pos1 = pos2 = 1
// for i in range(n * 2):
//     if i % 2:
//         length += abs(pos2 - a[i].id)
//         pos2 = a[i].id
//     else:
//         length += abs(pos1 - a[i].id)
//         pos1 = a[i].id
// print(length)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Building the pairs array is linear; Sort's own cost via the standard
// T(k) = T(k/2) + T(k-k/2) + k recurrence, bounded O(k log k) -- precedent
// solutions-proved/1871/1871_156.dfy. The scan loop is linear and dominated.

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

method Solve(n: int, edges_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |edges_list| * (CeilLog2(|edges_list|) + 1) + 8 * |edges_list| + |output| + 10
{
  steps := 1;
  var a := edges_list;
  var pairs: seq<(int, int)> := seq(|a|, i requires 0 <= i < |a| => (a[i], i + 1));
  steps := steps + |a| + 1;
  var sorted := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0);
  SortCostNLogN(|pairs|);
  steps := steps + SortCost(|pairs|);
  var length := 0;
  var pos1 := 1;
  var pos2 := 1;
  var i := 0;
  ghost var base1 := steps;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant steps <= base1 + 4 * i
    decreases |sorted| - i
  {
    var id := sorted[i].1;
    if i % 2 == 1 {
      length := length + AbsInt(pos2 - id);
      pos2 := id;
    } else {
      length := length + AbsInt(pos1 - id);
      pos1 := id;
    }
    i := i + 1;
    steps := steps + 4;
  }
  assert |pairs| == |edges_list| && |sorted| == |pairs|;
  assert steps <= base1 + 4 * |edges_list|;
  output := IntToString(length);
  steps := steps + |output| + 2;
}
