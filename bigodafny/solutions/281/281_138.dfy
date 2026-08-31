// 389_A. Fox and Number Game  (problem 281, solution 281_138)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// x = list(sorted(map(int, input().split())))
// 
// 
// def gcd(a, b):
//     while b > 0:
//         a, b = b, a % b
//     return a
// 
// tgcd = x.pop(0)
// for i in x:
//     tgcd = gcd(tgcd, i)
// 
// print(tgcd * n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
