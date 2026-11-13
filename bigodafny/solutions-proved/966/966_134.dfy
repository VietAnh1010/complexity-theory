// 596_A. Wilbur and Swimming Pool  (problem 966, solution 966_134)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// x = []
// y = []
// for i in range(n):
//     xi, yi = map(int, input().split())
//     x.append(xi)
//     y.append(yi)
// if n==1:
//     print(-1)
// 
// if n>=2:
//     s = (max(x) - min(x)) * (max(y) - min(y))
//     if s == 0: s = -1
//     print(s)
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function ColLen(values: seq<seq<string>>, i: nat): nat
  requires i <= |values|
  requires forall k :: 0 <= k < |values| ==> |values[k]| >= 2
{
  if i == 0 then 0 else ColLen(values, i - 1) + |values[i - 1][0]| + |values[i - 1][1]|
}

method Solve(n: int, values: seq<seq<string>>) returns (output: string, ghost steps: nat)
  requires 1 <= n <= 4
  requires |values| == n
  requires forall k :: 0 <= k < n ==> |values[k]| >= 2
  ensures steps <= 14 * n + 20 + ColLen(values, n) + |output|
{
  steps := 1;
  if n == 1 {
    output := "-1";
    steps := steps + 3;
  } else {
    var xs: seq<int> := [];
    var ys: seq<int> := [];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |xs| == i
      invariant |ys| == i
      invariant steps == 1 + 10 * i + ColLen(values, i)
      decreases n - i
    {
      xs := xs + [ParseInt(values[i][0])];
      ys := ys + [ParseInt(values[i][1])];
      i := i + 1;
      steps := steps + 10 + |values[i - 1][0]| + |values[i - 1][1]|;
    }
    steps := steps + 4 * n + 6;
    var s := (MaxSeq(xs) - MinSeq(xs)) * (MaxSeq(ys) - MinSeq(ys));
    if s == 0 { s := -1; }
    output := IntToString(s);
    IntToStringDigits(s);
    steps := steps + Digits(s);
  }
}
