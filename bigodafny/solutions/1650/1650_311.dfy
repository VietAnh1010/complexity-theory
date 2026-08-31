// 248_A. Cupboards  (problem 1650, solution 1650_311)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// left = []
// right = []
// 
// for i in range(n):
//     l, r = input().split()
// 
//     left.append(l)
//     right.append(r)
// 
// left_0 = left.count('0')
// left_1 = left.count('1')
// right_0 = right.count('0')
// right_1 = right.count('1')
// 
// print (min(left_0, left_1) + min(right_0, right_1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<string>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
