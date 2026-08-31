// 357_A. Group of Students  (problem 894, solution 894_3)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// m = int(input())
// cs = list(map(int, input().split()))
// l, r = map(int, input().split())
// s = sum(cs)
// ps = 0
// for i, a in enumerate(cs):
//     ps += a
//     if(l <= ps <= r and l <= (s-ps) <= r):
//         print(i+2)
//         break
// else:
//     print(0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, x: int, y: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
