// 1328_A. Divisibility Problem  (problem 171, solution 171_0)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for i in range(0,t):
//     a,b=input().split()
//     a=int(a)
//     b=int(b)
//     print((b-a%b)%b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
  requires n >= 0
  requires |pairs| == n
  requires forall idx :: 0 <= idx < |pairs| ==> |pairs[idx]| >= 2 && pairs[idx][1] != 0
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var pair := pairs[i];
    var a := pair[0];
    var b := pair[1];
    var r := (b - a % b) % b;
    parts := parts + [IntToString(r)];
    i := i + 1;
  }
  output := Join(parts, "\n");
}
