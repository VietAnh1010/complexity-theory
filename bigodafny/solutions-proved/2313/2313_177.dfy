// p02994 AtCoder Beginner Contest 131 - Bite Eating  (problem 2313, solution 2313_177)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N,L = map(int,input().split())
// x = []
//
// for i in range(1,N+1):
//     x.append(L+i-1)
//
// print(sum(x)-min(x,key = abs))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  requires a >= 0
  ensures steps <= 6 * a + 6
{
  var n := a;
  var l := b;
  var total := 0;
  var minAbsVal := 0;
  var minAbs := 0;
  var i := 1;
  steps := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant steps <= 6 * (i - 1) + 1
    decreases n - i
  {
    var v := l + i - 1;
    total := total + v;
    if i == 1 || AbsInt(v) < minAbs {
      minAbs := AbsInt(v);
      minAbsVal := v;
    }
    i := i + 1;
    steps := steps + 6;
  }
  output := IntToString(total - minAbsVal);
  steps := steps + 1;
}
