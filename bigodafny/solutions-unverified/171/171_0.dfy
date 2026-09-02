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
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var pair := pairs[i];
    assume {:axiom} |pair| >= 2;
    var a := pair[0];
    var b := pair[1];
    var r := (b - a % b) % b;
    parts := parts + [IntToString(r)];
    i := i + 1;
  }
  output := Join(parts, "\n");
}
