// 1349_A. Orac and LCM  (problem 1871, solution 1871_156)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import gcd
//
// n = int(input())
// lst = list(map(int, input().split()))
//
// lst.sort()
//
// g = gcd(lst[0],lst[1])
// l = int((lst[0]*lst[1])/(g))
//
// for i in range(2,n):
//     l = gcd(l , int((lst[i]*g)/gcd(g,lst[i])))
//     g = gcd(g, lst[i])
//
// print(l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma GcdNonneg(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures Gcd(a, b) >= 0
  decreases b
{
  if b == 0 {
  } else {
    GcdNonneg(b, a % b);
  }
}

lemma GcdPositive(a: int, b: int)
  requires a >= 0 && b >= 0
  requires a >= 1 || b >= 1
  ensures Gcd(a, b) >= 1
  decreases b
{
  if b == 0 {
  } else {
    GcdPositive(b, a % b);
  }
}

// Gcd is not a seq/string recursion; not covered by the charge table's rows.
// Following the precedent in solutions-proved/1871/1871_291.dfy, each Gcd
// call is charged 1: an opaque unit-cost primitive.

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

lemma NMonoBound(i: int, m: int, K: int)
  requires 2 <= i <= m
  requires K >= 0
  ensures K * (i - 2) <= K * m
{
  MulMonoRight(K, i - 2, m);
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| >= 2
  requires n <= |a_list|
  requires forall v :: v in a_list ==> v >= 1
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 6 * |a_list| + 12
{
  var lst := SortInts(a_list);
  SortIntsKeepsElems(a_list);
  SortCostNLogN(|a_list|);
  steps := 1 + SortCost(|a_list|);
  assert {:split_here} forall v :: v in lst ==> v >= 1;
  assert lst[0] in lst && lst[1] in lst;
  assert lst[0] >= 1 && lst[1] >= 1;
  var g := Gcd(lst[0], lst[1]);
  GcdPositive(lst[0], lst[1]);
  assert {:split_here} g >= 1;
  var l := (lst[0] * lst[1]) / g;
  assert {:split_here} l >= 0;
  steps := steps + 4;
  ghost var base1 := steps;
  var i := 2;
  while i < n
    invariant 2 <= i
    invariant i <= |a_list|
    invariant g >= 1
    invariant l >= 0
    invariant steps == base1 + 6 * (i - 2)
    decreases n - i
  {
    assert {:split_here} lst[i] in lst;
    assert lst[i] >= 1;
    var gi := Gcd(g, lst[i]);
    GcdPositive(g, lst[i]);
    assert {:split_here} gi >= 1;
    var running := (lst[i] * g) / gi;
    assert {:split_here} running >= 0;
    GcdNonneg(l, running);
    l := Gcd(l, running);
    g := Gcd(g, lst[i]);
    i := i + 1;
    steps := steps + 6;
  }
  output := IntToString(l);
  steps := steps + 1;
  NMonoBound(i, |a_list|, 6);
  assert steps <= base1 + 6 * |a_list| + 1;
}
