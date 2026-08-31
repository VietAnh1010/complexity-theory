// 1084_B. Kvass and the Fair Nut  (problem 2514, solution 2514_176)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n, s = map(int, input().split())
// v = list(map(int, input().split()))
// least = min(v)
// if sum(v) < s:
//     print(-1)
// else:
//     for i in v:
//         s -= (i-least)
//     if s > 0:
//         least -= ((s+n-1)/n)
//     print(math.ceil(least))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
