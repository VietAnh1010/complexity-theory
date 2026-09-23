// 1084_B. Kvass and the Fair Nut  (problem 2514, solution 2514_176)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n, s = map(int, input().split())
// v = list(map(int, input().split()))
// least = min(v)
// if sum(v) < s:
//     print(-1)
// else:
//     for i in v:
//         s -= (i-least)
//     if s > 0:
//         least -= ((s+n-1)/n)
//     print(math.ceil(least))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |c_list| >= 1
  requires a >= 1
  ensures steps <= 5 * |c_list| + |output| + 12
{
  var least := MinSeq(c_list);
  var total := SumSeq(c_list);
  steps := 1 + |c_list| + |c_list|;
  if total < b {
    output := "-1";
    steps := steps + 3;
  } else {
    var s := b;
    var i := 0;
    ghost var base1 := steps;
    while i < |c_list|
      invariant 0 <= i <= |c_list|
      invariant steps <= base1 + 3 * i
      decreases |c_list| - i
    {
      s := s - (c_list[i] - least);
      i := i + 1;
      steps := steps + 3;
    }
    if s > 0 {
      var res := least - FloorDiv(s + a - 1, a);
      output := IntToString(res);
      steps := steps + |output| + 3;
    } else {
      output := IntToString(least);
      steps := steps + |output| + 2;
    }
  }
}
