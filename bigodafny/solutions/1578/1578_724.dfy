// 1236_A. Stones  (problem 1578, solution 1578_724)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for i in range(int(input())):
//     a, b, c = map(int, input().split())
//     res = 0
//     while True:
//         if b >= 1 and c >= 2:
//             res += 3
//             c -= 2
//             b -= 1
//         elif a >= 1 and b >= 2:
//             res += 3
//             a -= 1
//             b -= 2
//         else:
//             print(res)
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
  requires n >= 0
  requires |matrix| >= n
  requires forall k :: 0 <= k < |matrix| ==> |matrix[k]| >= 3
  requires forall k :: 0 <= k < |matrix| ==> matrix[k][0] >= 0 && matrix[k][1] >= 0 && matrix[k][2] >= 0
{
  var lines: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    decreases n - t
  {
    var a := matrix[t][0];
    var b := matrix[t][1];
    var c := matrix[t][2];
    var res := 0;
    while true
      invariant a >= 0 && b >= 0 && c >= 0
      decreases a + b + c
    {
      if b >= 1 && c >= 2 {
        res := res + 3;
        c := c - 2;
        b := b - 1;
      } else if a >= 1 && b >= 2 {
        res := res + 3;
        a := a - 1;
        b := b - 2;
      } else {
        break;
      }
    }
    lines := lines + [IntToString(res)];
    t := t + 1;
  }
  output := Join(lines, "\n");
}
