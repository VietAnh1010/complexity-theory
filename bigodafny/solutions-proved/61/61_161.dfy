// 1042_A. Benches  (problem 61, solution 61_161)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// m = int(input())
//
// a = []
// _sum = 0
// for i in range(n):
//     j = int(input())
//     a.append(j)
//     _sum += j
// #print(a)
// a = sorted(a)
// if n == 1:
//     print(m + a[0], m + a[0])
// else:
//     _max = m + a[-1]
//     temp = a[-1] * n
//     if temp- _sum >= m:
//         print(a[-1], _max)
//     else:
//         m -= temp - _sum
//         _min = a[-1] + (int(m / n))
//         if m % n != 0:
//             _min += 1
//         print(_min, _max)
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

method Solve(n: int, k: int, ignored_lines: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1
  requires |ignored_lines| == n
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + n + 15
{
  SortCostNLogN(n);
  var a := SortInts(ignored_lines);
  var sum := SumSeq(a);
  steps := 1 + SortCost(n) + |a|;
  if n == 1 {
    output := IntToString(k + a[0]) + " " + IntToString(k + a[0]) + "\n";
    steps := steps + 4;
  } else {
    var mx := k + a[n-1];
    var temp := a[n-1] * n;
    steps := steps + 3;
    if temp - sum >= k {
      output := IntToString(a[n-1]) + " " + IntToString(mx) + "\n";
      steps := steps + 4;
    } else {
      var m := k - (temp - sum);
      var mn := a[n-1] + (m / n);
      steps := steps + 3;
      if m % n != 0 {
        mn := mn + 1;
        steps := steps + 1;
      }
      output := IntToString(mn) + " " + IntToString(mx) + "\n";
      steps := steps + 4;
    }
  }
}
