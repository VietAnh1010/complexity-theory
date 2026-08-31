// 208_D. Prizes, Prizes, more Prizes  (problem 1092, solution 1092_0)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import bisect
// 
// n = int(input())
// a = [int(x) for x in input().split()]
// p = [int(x) for x in input().split()]
// b = [0, 0, 0, 0, 0]
// s = 0
// for i in a:
//     s += i
//     k = bisect.bisect_right(p, s)
//     while k != 0:
//         if (k == 5) or (p[k] > s):
//             k -= 1
//         b[k] += s // p[k]
//         s %= p[k]
//         k = bisect.bisect_right(p, s)
// print(' '.join(list(map(str, b))))
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
