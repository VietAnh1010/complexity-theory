// 192_A. Funky Numbers  (problem 2065, solution 2065_24)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// bruh = set([(i+1)*i/2 for i in range(1, 50001)])
// n = int(input())
// if any(n-t in bruh for t in bruh):
//     print('YES')
// else:
//     print('NO')
// ###### thanking telegram for solutions ######
// '''__________ ____ ___  _____________  __.___ 
// \______   \    |   \/   _____/    |/ _|   |
//  |       _/    |   /\_____  \|      < |   |
//  |    |   \    |  / /        \    |  \|   |
//  |____|_  /______/ /_______  /____|__ \___|
// '''
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
