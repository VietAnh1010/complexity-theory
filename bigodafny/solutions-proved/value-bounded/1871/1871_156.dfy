// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   This proof's bound depends on the MAGNITUDE of an input, not only on how
//   many inputs there are. BigOBench fitted the label by profiling, which
//   treats a capped value as constant; COMPLEXITY.md section 1 decides the
//   opposite, so the two disagree here by construction.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
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

include "../../../prelude.dfy"

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

lemma MulDivBounds(x: int, y: int, g: int)
  requires x >= 0 && y >= 0 && g >= 1
  ensures x * y >= 0 && (x * y) / g >= 0
  ensures x >= 1 && 1 <= g <= y ==> 1 <= (x * y) / g <= x * y
{
  CostMulMono(x, 0, y);
  var p := x * y;
  var q := p / g;
  assert p == g * q + p % g && 0 <= p % g < g;
  if q < 0 {
    CostMulMonoLeft(1, g, -q);
    assert false;
  }
  if x >= 1 && 1 <= g <= y {
    CostMulMonoLeft(1, x, y);
    assert q != 0;
    CostMulMonoLeft(1, g, q);
  }
}

lemma IterCost(c: int, x: int, l: int, r: int, l0: int, m: int)
  requires c >= 0 && 1 <= x <= m && 1 <= l <= l0 && r >= 0
  ensures 2 * GcdSteps(c, x) + GcdSteps(l, r) <= 4 * BitLen(m) + 7 + 2 * BitLen(l0)
{
  GcdStepsBound(c, x);
  CeilLog2Monotone(x + 1, m + 1);
  GcdStepsBoundFirst(l, r);
  CeilLog2Monotone(l + 1, l0 + 1);
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires |a_list| >= 2
  requires n <= |a_list|
  requires forall v :: v in a_list ==> v >= 1
  ensures steps <= 2 * NLogN(|a_list|)
                   + |a_list| * (15 + 4 * BitLen(MaxSeq(a_list))
                                 + 2 * BitLen(MaxSeq(a_list) * MaxSeq(a_list)))
                   + 2 * BitLen(MaxSeq(a_list)) + |output| + 10
{
  steps := 0;
  steps := steps + SortCost(|a_list|);
  var lst := SortInts(a_list);
  SortIntsKeepsElems(a_list);
  SortCostWithin(|a_list|, |a_list|);
  MaxSeqBound(a_list);
  ghost var M := MaxSeq(a_list);
  ghost var L := BitLen(M);
  assert {:split_here} forall v :: v in lst ==> v >= 1;
  assert {:split_here} forall v :: v in lst ==> 1 <= v <= M;
  assert lst[0] in lst && lst[1] in lst;
  assert lst[0] >= 1 && lst[1] >= 1;
  steps := steps + (2 + GcdSteps(lst[0], lst[1]));
  var g := Gcd(lst[0], lst[1]);
  GcdLeSecond(lst[0], lst[1]);
  CeilLog2Monotone(lst[1] + 1, M + 1);
  GcdStepsBound(lst[0], lst[1]);
  GcdPositive(lst[0], lst[1]);
  assert {:split_here} g >= 1;
  steps := steps + 4;
  MulDivBounds(lst[0], lst[1], g);
  var l := lst[0] * lst[1] / g;
  assert {:split_here} l >= 0;
  ghost var l0 := l;
  CostMulMonoLeft(lst[0], M, lst[1]);
  CostMulMono(M, lst[1], M);
  CeilLog2Monotone(l0 + 1, M * M + 1);
  ghost var P := BitLen(M * M);
  assert BitLen(l0) <= P;
  ghost var K := 15 + 4 * L + 2 * P;
  ghost var base1 := steps;
  var i := 2;
  while i < n
    invariant 2 <= i
    invariant i <= |a_list|
    invariant g >= 1
    invariant l >= 0
    invariant 1 <= l <= l0
    invariant steps <= base1 + K * (i - 2)
    decreases n - i
  {
    steps := steps + 2;
    assert {:split_here} lst[i] in lst;
    assert lst[i] >= 1;
    steps := steps + (1 + GcdSteps(g, lst[i]));
    var gi := Gcd(g, lst[i]);
    GcdPositive(g, lst[i]);
    assert {:split_here} gi >= 1;
    steps := steps + 3;
    MulDivBounds(lst[i], g, gi);
    var running := lst[i] * g / gi;
    assert {:split_here} running >= 0;
    GcdNonneg(l, running);
    IterCost(g, lst[i], l, running, l0, M);
    steps := steps + GcdSteps(l, running);
    GcdLeFirst(l, running);
    l := Gcd(l, running);
    steps := steps + (1 + GcdSteps(g, lst[i]));
    g := Gcd(g, lst[i]);
    steps := steps + 1;
    assert K * (i + 1 - 2) == K * (i - 2) + K;
    i := i + 1;
  }
  CostMulMono(K, i - 2, |a_list|);
  steps := steps + 1;
  steps := steps + Digits(l);
  IntToStringDigits(l);
  output := IntToString(l);
}

import opened Prelude
