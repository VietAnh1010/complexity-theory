// 886_C. Petya and Catacombs  (problem 2505, solution 2505_87)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = list(map(int, input().split()))
// arr.sort()
// cnt_total = 0
// cnt_tmp = 0
// for i in range(1,n):
//     if arr[i] == arr[i-1]:
//         cnt_total +=1
// print(cnt_total+1)
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

method Solve(n: int, coordinates: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires |coordinates| >= 1
  requires n <= |coordinates[0]|
  requires n >= 0
  ensures steps <= 2 * |coordinates[0]| * (CeilLog2(|coordinates[0]|) + 1) + 3 * n + 4
{
  var arr := SortInts(coordinates[0]);
  SortCostNLogN(|coordinates[0]|);
  var cnt := 0;
  var i := 1;
  steps := 1 + SortCost(|coordinates[0]|);
  ghost var base1 := steps;
  while i < n
    invariant 1 <= i <= n + 1
    invariant |arr| == |coordinates[0]|
    invariant steps <= base1 + 3 * (i - 1)
    decreases n - i
  {
    if arr[i] == arr[i - 1] {
      cnt := cnt + 1;
    }
    i := i + 1;
    steps := steps + 3;
  }
  output := IntToString(cnt + 1);
  steps := steps + 1;
}
