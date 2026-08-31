// p03214 Dwango Programming Contest V - Thumbnail  (problem 1742, solution 1742_78)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// frame = list(map(int, input().split()))
// avg = sum(frame) / n
// ans= []
// for d in frame:
//     ans.append(abs(d-avg)) 
//     
// print(ans.index(min(ans)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
