// 672_A. Summer Camp  (problem 1467, solution 1467_233)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// t=''
// for i in range(n+100):
//     t+=str(i)
// print(t[n])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma IntToStringLen(x: int)
  ensures |IntToString(x)| >= 1
  decreases if x < 0 then 1 - x else x
{
  if x < 0 { IntToStringLen(-x); }
  else if x < 10 {
  } else {
    IntToStringLen(x / 10);
  }
}

lemma JoinEmptySepLen(parts: seq<string>)
  requires forall k :: 0 <= k < |parts| ==> |parts[k]| >= 1
  ensures |Join(parts, "")| >= |parts|
  decreases |parts|
{
  if |parts| == 0 {
  } else if |parts| == 1 {
  } else {
    JoinEmptySepLen(parts[1..]);
  }
}

method Solve(N: int) returns (output: string, ghost steps: nat)
  requires N >= 0
  ensures steps <= 5 * (N + 100) + 2 * ((N + 100) * Digits(N + 100)) + 3
{
  steps := 1;
  ghost var D := Digits(N + 100);
  ghost var sd: nat := 0;
  var parts: seq<string> := [];
  var i := 0;
  while i < N + 100
    invariant 0 <= i
    invariant |parts| == i
    invariant forall k :: 0 <= k < |parts| ==> |parts[k]| >= 1
    invariant i <= N + 100
    invariant SumLen(parts) == sd
    invariant sd <= i * D
    invariant steps <= 4 * i + sd + 1
    decreases N + 100 - i
  {
    IntToStringLen(i);
    IntToStringDigits(i);
    DigitsMono(i, N + 100);
    CostMulDistrib(i, 1, i + 1, D);
    SumLenSnoc(parts, IntToString(i));
    sd := sd + Digits(i);
    steps := steps + 4 + Digits(i);
    parts := parts + [IntToString(i)];
    i := i + 1;
  }
  JoinEmptySepLen(parts);
  steps := steps + SumLen(parts) + |parts|;
  var t := Join(parts, "");
  output := [t[N]];
  steps := steps + 2;
  CostMulDistrib(N + 100, 0, N + 100, D);
}
