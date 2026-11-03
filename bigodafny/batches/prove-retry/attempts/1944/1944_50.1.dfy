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

include "../../prelude.dfy"
import opened Prelude

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
  ensures steps <= 25 * x + 20
{
  steps := 1;
  if x <= 1 { r := x; steps := 2; return; }
  var hi := 1;
  steps := 2;
  while hi * hi < x
    invariant hi >= 1
    invariant hi <= 2 * x
    invariant steps <= 2 + 5 * hi
    decreases x - hi * hi
  {
    SelfLeSq1944(hi);
    hi := hi * 2;
    steps := steps + 5;
  }
  var lo := 0;
  ghost var s2 := steps;
  ghost var hi0 := hi;
  while lo < hi
    invariant 0 <= lo <= hi <= hi0
    invariant steps + 6 * (hi - lo) <= s2 + 6 * hi0
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if mid * mid >= x { hi := mid; } else { lo := mid + 1; }
    steps := steps + 6;
  }
  steps := steps + 1;
  return lo, steps;
}

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 40 * |numbers| + 25 * PosSum1944(numbers, |numbers|) + 10 + 2 * |output|
{
  steps := 1;
  var parts: seq<string> := [];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |parts| == i
    invariant steps <= 1 + 40 * i + 25 * PosSum1944(numbers, i) + SumLen(parts)
    decreases |numbers| - i
  {
    var r, cs := CeilSqrt(if numbers[i] >= 0 then numbers[i] else 0);
    IntToStringDigits(r);
    SumLenSnoc(parts, IntToString(r));
    parts := parts + [IntToString(r)];
    i := i + 1;
    steps := steps + cs + 8 + |parts[i - 1]| ;
  }
  if |parts| > 0 { JoinLen(parts, "\n"); }
  output := Join(parts, "\n") + "\n";
  steps := steps + SumLen(parts) + |parts| + 1;
}
