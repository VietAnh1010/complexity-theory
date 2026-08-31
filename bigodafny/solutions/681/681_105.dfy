// p03683 AtCoder Regular Contest 076 - Reconciled?  (problem 681, solution 681_105)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// mod=10**9+7
// 
// 
// def main():
//     n, m = map(int, input().split())
//     if abs(n - m) > 1:
//         return 0
// 
// 
//     fact = 1
//     for i in range(1, min(n, m) + 1):
//         fact = fact * i % mod
// 
// 
// 
//     if n == m:
//         return fact ** 2 * 2 % mod
//     else:
//         return fact * fact * (min(n, m) + 1) % mod
// 
// 
// 
// 
// print(main())
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
