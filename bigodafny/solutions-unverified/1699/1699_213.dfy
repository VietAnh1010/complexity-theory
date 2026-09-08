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
  // the seed [0,1] repeats 1 once, so the last term is not yet strictly
  // increasing; the second component retires that one step.
  while fib[|fib| - 1] <= n
    invariant |fib| >= 2
    invariant fib[|fib| - 2] >= 0
    invariant fib[|fib| - 1] >= 1
    decreases n - fib[|fib| - 1] + 1, if fib[|fib| - 2] == 0 then 1 else 0
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
      invariant 0 <= k <= |fib|
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
