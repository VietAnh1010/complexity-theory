// 768_A. Oath of the Night's Watch  (problem 1997, solution 1997_199)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = [int(x) for x in input().split()]
// ans, mi, ma = 0, min(arr), max(arr)
// for x in arr:
//   if not (x == mi or x == ma):
//     ans += 1
// print(ans)
// 		 	 	  				 	  								 		
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
