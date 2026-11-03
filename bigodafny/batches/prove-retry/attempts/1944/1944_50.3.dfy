// 1550_A. Find The Array  (problem 1944, solution 1944_50)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// t=int(input())
// for i in range(t):
//     print(math.ceil(math.sqrt(int(input()))))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma SelfLeSq1944(j: int)
  requires j >= 1
  ensures j <= j * j
{
}

ghost function PosSum1944(a: seq<int>, k: nat): nat
  requires k <= |a|
  decreases k
{
  if k == 0 then 0 else PosSum1944(a, k - 1) + (if a[k - 1] > 0 then a[k - 1] else 0)
}

method CeilSqrt(x: int) returns (r: int, ghost steps: nat)
  requires x >= 0
  ensures r >= 0
  ensures steps <= 22 * x + 8
{
  steps := 0;
  steps := steps + 1;
  if x <= 1 {
    r := x;
    return;
  }
  var hi := 1;
  while hi * hi < x
    invariant hi >= 1
    invariant hi <= 2 * x
    invariant steps <= 1 + 4 * hi
    decreases x - hi * hi
  {
    SelfLeSq1944(hi);
    steps := steps + 3;
    steps := steps + 1;
    hi := hi * 2;
  }
  steps := steps + 2;
  var lo := 0;
  ghost var s2 := steps;
  ghost var hi0 := hi;
  while lo < hi
    invariant 0 <= lo <= hi
    invariant hi <= hi0
    invariant steps + 7 * (hi - lo) <= s2 + 7 * hi0
    decreases hi - lo
  {
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
  }
  steps := steps + 1;
  r := lo;
  return;
}

method Solve(n: int, numbers: seq<int>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 18 * |numbers| + 22 * PosSum1944(numbers, |numbers|) + 2 * |output| + 3
{
  steps := 0;
  var parts: seq<string> := [];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |parts| == i
    invariant steps <= 18 * i + 22 * PosSum1944(numbers, i) + SumLen(parts)
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
    i := i + 1;
  }
  steps := steps + 2;
  steps := steps + (SumLen(parts) + |parts| + |"\n"|);
  if |parts| > 0 { JoinLen(parts, "\n"); }
  output := Join(parts, "\n") + "\n";
}

import opened Prelude
