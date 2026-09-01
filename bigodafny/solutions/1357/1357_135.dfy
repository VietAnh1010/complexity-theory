// 1331_B. Limericks  (problem 1357, solution 1357_135)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// 
// n = int(sys.stdin.readline().strip())
// L = []
// i = 2
// while n > 1:
//     if n % i == 0:
//         L.append(str(i))
//         n = n // i
//     else:
//         i = i + 1
// print("".join(L))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
{

  var m := n;
  var i := 2;
  var parts: seq<string> := [];
  while m > 1
    decreases m
  {
    if m % i == 0 {
      parts := parts + [IntToString(i)];
      m := m / i;
    } else {
      i := i + 1;
    }
  }
  output := Join(parts, "");
}
}
