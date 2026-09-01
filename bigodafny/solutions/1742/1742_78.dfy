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
  var total := SumSeq(a_list);
  var bestIdx := 0;
  var bestVal := AbsInt(a_list[0] * n - total);
  var i := 1;
  while i < n
    decreases n - i
  {
    var val := AbsInt(a_list[i] * n - total);
    if val < bestVal {
      bestVal := val;
      bestIdx := i;
    }
    i := i + 1;
  }
  output := IntToString(bestIdx);
}
