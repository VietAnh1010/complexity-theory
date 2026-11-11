// --- Python ---------------------------------------------------------
// import math
// t=int(input())
// for i in range(t):
//     print(math.ceil(math.sqrt(int(input()))))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma SqGe(h: nat)
  requires h >= 1
  ensures h <= h * h
{
  CostMulMono(h, 1, h);
}

lemma DblLog(h: nat)
  requires h >= 1
  ensures CeilLog2(2 * h) == 1 + CeilLog2(h)
{
  assert (2 * h + 1) / 2 == h;
}

lemma SqrtLogFacts(x: nat, hi0: nat)
  requires x >= 2 && 1 <= hi0 <= 2 * x
  ensures CeilLog2(hi0) <= CeilLog2(x + 1) + 1
{
  CeilLog2Monotone(hi0, 2 * x);
  DblLog(x);
  CeilLog2Monotone(x, x + 1);
}

method CeilSqrt(x: int) returns (r: int, ghost steps: nat)
  requires x >= 0
  ensures r >= 0
  ensures steps <= 11 * CeilLog2(x + 1) + 22
{
  steps := 0;
  steps := steps + 1;
  if x <= 1 {
    return x, steps;
  }
  var hi := 1;
  ghost var it1: nat := 0;
  while hi * hi < x
    invariant hi >= 1
    invariant hi <= 2 * x
    invariant it1 <= CeilLog2(hi)
    invariant steps <= 1 + 4 * it1
    decreases x - hi * hi
  {
    SqGe(hi);
    DblLog(hi);
    steps := steps + 3;
    steps := steps + 1;
    hi := hi * 2;
    it1 := it1 + 1;
  }
  steps := steps + 2;
  ghost var hi0 := hi;
  SqrtLogFacts(x, hi0);
  var lo := 0;
  ghost var it2: nat := 0;
  while lo < hi
    invariant 0 <= lo <= hi
    invariant it2 + SearchPot(hi - lo) <= SearchPot(hi0)
    invariant steps <= 3 + 4 * it1 + 7 * it2
    decreases hi - lo
  {
    ghost var k := hi - lo;
    steps := steps + 2;
    steps := steps + 2;
    var mid := (lo + hi) / 2;
    steps := steps + 2;
    if mid * mid >= x {
      hi := mid;
    } else {
      steps := steps + 1;
      lo := mid + 1;
    }
    BisectStep(k, hi - lo);
    it2 := it2 + 1;
  }
  assert SearchPot(hi0) == CeilLog2(hi0) + 1;
  steps := steps + 1;
  return lo, steps;
}

method Solve(n: int, numbers: seq<int>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 33 * |numbers| + 11 * SumLog(numbers, |numbers|) + 2 * |output| + 3
{
  steps := 0;
  var parts: seq<string> := [];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |parts| == i
    invariant steps <= 32 * i + 11 * SumLog(numbers, i) + SumLen(parts)
    decreases |numbers| - i
  {
    steps := steps + 3;
    steps := steps + (3 + if numbers[i] >= 0 then 1 else 0);
    var r, s0 := CeilSqrt(if numbers[i] >= 0 then numbers[i] else 0);
    steps := steps + s0;
    steps := steps + (1 + Digits(r) + |[IntToString(r)]|);
    IntToStringDigits(r);
    SumLenSnoc(parts, IntToString(r));
    parts := parts + [IntToString(r)];
    steps := steps + 1;
    assert SumLog(numbers, i + 1) == SumLog(numbers, i) + BitLen(numbers[i]);
    i := i + 1;
  }
  steps := steps + 2;
  steps := steps + (SumLen(parts) + |parts| + |"\n"|);
  output := Join(parts, "\n") + "\n";
  if |parts| >= 1 {
    JoinLen(parts, "\n");
  }
  assert |"\n"| == 1;
}

import opened Prelude
