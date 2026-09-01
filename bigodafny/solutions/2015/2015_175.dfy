// 463_B. Caisa and Pylons  (problem 2015, solution 2015_175)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// h = [int(x) for x in input().split()]
// 
// ans = 0
// for i in h:
//     ans = max(ans,i)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string)
{
  var h := ParseInts(a_list);
  var ans := 0;
  var i := 0;
  while i < |h|
    decreases |h| - i
  {
    if h[i] > ans { ans := h[i]; }
    i := i + 1;
  }
  output := IntToString(ans);
}
