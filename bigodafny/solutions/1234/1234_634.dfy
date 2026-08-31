// 1372_B. Omkar and Last Class of Math  (problem 1234, solution 1234_634)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def factors(n):
//     i = 1
//     while i * i <= n:
//         if n % i == 0:
//             yield i
//             yield n // i
//         i += 1
// 
// for t in range(int(input())):
//     n = int(input())
//     s = sorted(list(factors(n)))[-2]
//     print(s, n - s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
