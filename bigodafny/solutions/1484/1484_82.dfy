// 172_A. Phone Code  (problem 1484, solution 1484_82)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// cases = int(input())
// 
// numbers = []
// while cases:
//     cases -= 1
//     s = input()
//     numbers.append(s)
// 
// numbers.sort()
// 
// ct = 0
// 
// for i, j in zip(numbers[0], numbers[-1]):
//     if i == j:
//         ct += 1
//     else:
//         print(ct)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<string>) returns (output: string)
{
  var sorted := SortStrings(numbers);
  var first := sorted[0];
  var last := sorted[|sorted|-1];
  var ct := 0;
  var i := 0;
  while i < |first| && i < |last| && first[i] == last[i]
    decreases |first| - i
  {
    ct := ct + 1;
    i := i + 1;
  }
  output := IntToString(ct);
}
