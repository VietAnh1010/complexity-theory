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
  output := ""; // TODO: translate the Python above
}
