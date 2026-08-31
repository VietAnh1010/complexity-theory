// 889_A. Petya and Catacombs  (problem 1367, solution 1367_88)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// b = [0] * (n + 1)
// res = 1
// b[1] = 1
// for i in range(2, n + 1) :
//     if b[a[i - 1]] == 0 :
//         b[i] = 1
//         res += 1
//     else :
//         b[i] = 1
//         b[a[i - 1]] = 0
// print(res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
