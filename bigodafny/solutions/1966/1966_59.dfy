// 25_B. Phone numbers  (problem 1966, solution 1966_59)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// num = input()
// 
// res = []
// if n % 2 == 0:
//     for i in range(0, n, 2):
//         res.append(num[i:i+2])
// else:
//     for i in range(0, n-3, 2):
//         res.append(num[i:i+2])
//     res.append(num[n-3:])
// 
// print('-'.join(res))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  var res: seq<string> := [];
  if n % 2 == 0 {
    var i := 0;
    while i < n
      decreases n - i
    {
      res := res + [s[i..i+2]];
      i := i + 2;
    }
  } else {
    var i := 0;
    while i < n - 3
      decreases (n - 3) - i
    {
      res := res + [s[i..i+2]];
      i := i + 2;
    }
    res := res + [s[n-3..]];
  }
  output := Join(res, "-");
}
