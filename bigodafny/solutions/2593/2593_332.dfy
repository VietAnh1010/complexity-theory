// 991_B. Getting an A  (problem 2593, solution 2593_332)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// L = list(map(int, input().split()))
// L = sorted(L)
// s = sum(L)
// c = 0
// p = s/n
// if p >= 4.5:
//     print(0)
// else:
//     for i in range(n):
//         s = s-L[i]+5
//         c += 1
//         if s/n >= 4.5:
//             print(c)
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
