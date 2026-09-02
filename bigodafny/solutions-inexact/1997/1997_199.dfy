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
  var mi := MinSeq(a_list);
  var ma := MaxSeq(a_list);
  var ans := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    if !(a_list[i] == mi || a_list[i] == ma) {
      ans := ans + 1;
    }
    i := i + 1;
  }
  output := IntToString(ans);
}
