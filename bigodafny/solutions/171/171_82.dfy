// 1328_A. Divisibility Problem  (problem 171, solution 171_82)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// num = int(input())
// 
// for i in range(num):
//     l = input().split()
//     a = int(l[0])
//     b = int(l[1])
// 
//     if a % b == 0:
//         print(0)
//     else:
//         print(int(b - (a % b)))
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
    var l := pairs[i];
    var a := l[0];
    var b := l[1];
    if a % b == 0 {
      parts := parts + [IntToString(0)];
    } else {
      parts := parts + [IntToString(b - (a % b))];
    }
    i := i + 1;
  }
  output := Join(parts, "\n");
}
