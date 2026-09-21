// 1201_B. Zero Array  (problem 2010, solution 2010_401)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// inp = input()
// a=[int(ele) for ele in inp.split()]
// a.sort()
// count=0
// for ele in a:
//     if ele%2!=0:
//         count += 1
// if sum(a[:n-1]) < a[-1]:
//     print('NO')
// elif count%2==0:
//     print('YES')
// else:
//     print('NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the O(n log n) sort -----------------
ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1 else SortCost(k / 2) + SortCost(k - k / 2) + k
}

ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(m: nat, n: nat)
  requires m <= n
  ensures CeilLog2(m) <= CeilLog2(n)
  decreases n
{
  if n <= 1 { } else if m <= 1 { } else { CeilLog2Monotone((m + 1) / 2, (n + 1) / 2); }
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
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 1 + 4 * n + 10
{
  SortCostNLogN(n);
  steps := 1 + SortCost(n);
  var a := SortInts(a_list);
  var count := 0;
  var i := 0;
  ghost var base1 := steps;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant steps <= base1 + 2 * i
    decreases |a| - i
  {
    if a[i] % 2 != 0 {
      count := count + 1;
    }
    i := i + 1;
    steps := steps + 2;
  }
  assert steps <= base1 + 2 * n;
  var prefixSum := SumSeq(a[..n-1]);
  steps := steps + (n - 1) + 1;
  if prefixSum < a[n-1] {
    output := "NO";
  } else if count % 2 == 0 {
    output := "YES";
  } else {
    output := "NO";
  }
  steps := steps + 2;
}
