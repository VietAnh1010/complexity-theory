// 1177_A. Digits Sequence (Easy Edition)  (problem 1501, solution 1501_224)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// number = int(input())
// count = 0
// while number-len(str(count+1)) >= 0:
//     number-=len(str(count+1))
//     count+=1
// if number==0:
//     count = str(count)
//     print(count[-1])
// else:
//     count+=1
//     count = str(count)
//     print(count[number-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
