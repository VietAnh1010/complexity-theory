// 918_A. Eleven  (problem 1699, solution 1699_213)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// fib = [0, 1]
// while fib[-1] <= n:
//     fib.append(fib[-1] + fib[-2])
// name = ''
// for i in range(1,n+1):
//     if i in fib:
//         name += 'O'
//     else:
//         name += 'o'
// print(name) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var fib := [0, 1];
  while fib[|fib| - 1] <= n
    decreases n - fib[|fib| - 1] + 1
  {
    fib := fib + [fib[|fib| - 1] + fib[|fib| - 2]];
  }
  var parts: seq<string> := [];
  var i := 1;
  while i <= n
    decreases n - i + 1
  {
    var isFib := false;
    var k := 0;
    while k < |fib|
      decreases |fib| - k
    {
      if fib[k] == i {
        isFib := true;
      }
      k := k + 1;
    }
    if isFib {
      parts := parts + ["O"];
    } else {
      parts := parts + ["o"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
