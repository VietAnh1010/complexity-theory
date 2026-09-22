// 667_B. Coat of Anticubism  (problem 2071, solution 2071_39)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// s = sum(a)
// t = 0
// a.sort(reverse = True)
// for i in a :
//     t += i
//     s -= i
//     if(t >= s) :
//         break
// 
// print(t - s + 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Sort's own cost via the standard T(k) = T(k/2) + T(k-k/2) + k recurrence,
// bounded O(k log k) -- precedent solutions-proved/1871/1871_156.dfy.
// SumSeq is a recursive prelude function over a_list: charged its length.
// The scan loop is linear and dominated by the sort.

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
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 6 * |a_list| + |output| + 10
{
  var a := Sort(a_list, (x: int, y: int) => x > y);
  SortCostNLogN(|a_list|);
  steps := 1 + SortCost(|a_list|);
  var s := SumSeq(a_list);
  steps := steps + |a_list| + 1;
  var t := 0;
  var idx := 0;
  var stopped := false;
  ghost var base1 := steps;
  while idx < |a| && !stopped
    invariant 0 <= idx <= |a|
    invariant steps <= base1 + 3 * idx
    decreases |a| - idx
  {
    var i := a[idx];
    t := t + i;
    s := s - i;
    if t >= s {
      stopped := true;
    }
    idx := idx + 1;
    steps := steps + 3;
  }
  assert |a| == |a_list|;
  assert steps <= base1 + 3 * |a_list|;
  output := IntToString(t - s + 1);
  steps := steps + |output| + 2;
}
