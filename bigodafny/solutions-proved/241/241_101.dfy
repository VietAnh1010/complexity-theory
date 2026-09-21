// 1038_D. Slime  (problem 241, solution 241_101)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int, input().split()))
// a.sort()
// if n==1:
//     print(a[0])
// else:
//     i=0
//     while i<n and a[i]<=0:
//         i+=1
//     if i==0:
//         print(sum(a)-2*a[0])
//     elif i==n:
//         print(2*a[-1]-sum(a))
//     else:
//         print(sum(a[i:])-sum(a[:i]))
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
  requires n >= 1 && n == |a_list|
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 4 * n + 10
{
  if n == 1 {
    output := IntToString(a_list[0]);
    steps := 2;
  } else {
    SortCostNLogN(n);
    steps := 1 + SortCost(n);
    var s := SortInts(a_list);
    var i := 0;
    while i < n && s[i] <= 0
      invariant 0 <= i <= n
      invariant steps <= 1 + SortCost(n) + 2 * i
      decreases n - i
    {
      i := i + 1;
      steps := steps + 2;
    }
    var ans: int;
    if i == 0 {
      ans := SumRange(s, 0, n) - 2 * s[0];
      steps := steps + n + 2;
    } else if i == n {
      ans := 2 * s[n - 1] - SumRange(s, 0, n);
      steps := steps + n + 2;
    } else {
      ans := SumRange(s, i, n) - SumRange(s, 0, i);
      steps := steps + (n - i) + i + 1;
    }
    output := IntToString(ans);
    steps := steps + 1;
  }
}

function SumRange(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0 else s[lo] + SumRange(s, lo + 1, hi)
}
