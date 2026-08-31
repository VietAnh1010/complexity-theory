// 624_B. Making a String  (problem 209, solution 209_29)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// rng = [int(t) for t in input().split()]
// 
// ans = 0
// while len(rng) != 0:
//     mx = max(rng)
// 
//     if mx <= 0:
//         break
// 
//     ans += mx
// 
//     rng.remove(mx)
//     for i in range(len(rng)):
//         if rng[i] == mx:
//             rng[i] -= 1
// 
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
