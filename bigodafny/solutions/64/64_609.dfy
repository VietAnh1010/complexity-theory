// 1234_B1. Social Network (easy version)  (problem 64, solution 64_609)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// a = [0] * k
// l = 0
// curr = set()
// 
// ids = map(int, input().split())
// 
// for id in ids:
//     if id not in curr:
//         curr.add(id)
// 
//         if a[-1] != 0:
//             curr.remove(a[-1])
// 
//         a[1:] = a[:-1]
//         a[0] = id
//         l = min(l + 1, k)
// 
// print(l)
// print(' '.join(map(str, a[:l])))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, ratings: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
