// 1331_B. Limericks  (problem 1357, solution 1357_271)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// i = 2
// while i * i <= n:
//     if n % i == 0:
//         print(i, end='')
//         print(n // i,end='')
//     i += 1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
{

  var i := 2;
  var parts: seq<string> := [];
  while i * i <= n
    decreases n - i*i
  {
    if n % i == 0 {
      parts := parts + [IntToString(i), IntToString(n / i)];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
}
