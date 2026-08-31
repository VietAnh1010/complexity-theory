// 1349_A. Orac and LCM  (problem 1871, solution 1871_291)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def gcd(a, b):
//     while b:
//         a, b = b, a % b
//     return a
// 
// def solve(array):
//     lcm = (array[0] * array[1])//gcd(array[0], array[1])
//     current = lcm
//     for i in range(2, len(array)):
//         running = (current * array[i])//gcd(current, array[i])
//         lcm = gcd(lcm, running)
//         current = gcd(current, array[i])
//     print(lcm)
//     return
// 
// n = int(input())
// arr = list(map(int, input().split(' ')))
// solve(arr)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
