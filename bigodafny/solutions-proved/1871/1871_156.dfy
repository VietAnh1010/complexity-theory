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

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

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
  SortCostTreeBound(|a_list|);
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
