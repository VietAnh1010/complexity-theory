// 1194_A. Remove a Progression  (problem 2627, solution 2627_428)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for k in range(t):
//     c=input()
//     n=int(c.split()[0])
//     x=int(c.split()[1])
//     print(2*x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, data: seq<seq<int>>) returns (output: string)
  requires n == |data|
  requires forall k :: 0 <= k < |data| ==> |data[k]| >= 2
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    lines := lines + [IntToString(2 * data[i][1])];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
