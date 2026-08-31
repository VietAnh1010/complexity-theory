// 9_C. Hexadecimal's Numbers  (problem 2381, solution 2381_176)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,ans=int(input()),1
// while int(bin(ans)[2:])<=n:
//     ans+=1
// print(ans-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
