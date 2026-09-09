// 873_A. Chores  (problem 1540, solution 1540_206)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k,x=map(int,input().split())
// a=list(map(int,input().split()))
// a.sort(reverse=True)
// for i in range(0,k):
//     a[i]=x
// print(sum(a))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(nlogn) -- agrees. SortInts dominates: the trailing loop is one
// pass over a prefix. Scaffolding is 187_193's, unchanged.
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

method Solve(n: int, a: int, b: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires |numbers| == n
  requires 0 <= a <= n
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 3 * n + 6
{
  SortCostNLogN(n);
  steps := 1 + SortCost(n);
  ghost var s0 := steps;
  var sortedA := SortInts(numbers);
  var keep := n - a;
  var total := 0;
  var i := 0;
  while i < keep
    invariant 0 <= i <= keep
    invariant steps == s0 + 3 * i
    decreases keep - i
  {
    total := total + sortedA[i];
    i := i + 1;
    steps := steps + 3;
  }
  total := total + a * b;
  output := IntToString(total);
  steps := steps + 4;
}
