// 25_A. IQ test  (problem 1093, solution 1093_628)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// numbers = list(map(int, input().split()))
// 
// evens = list()
// odds = list()
// 
// 
// def fill_evens():
//     for k in numbers:
//         if k % 2 == 0:
//             evens.append(k)
//         else:
//             odds.append(k)
// fill_evens()
// distinct = evens[0] if len(evens) == 1 else odds[0]
// print(numbers.index(distinct) + 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var countEven := 0;
  var countOdd := 0;
  var idxEven := 0;
  var idxOdd := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    if a_list[i] % 2 == 0 {
      countEven := countEven + 1;
      idxEven := i;
    } else {
      countOdd := countOdd + 1;
      idxOdd := i;
    }
    i := i + 1;
  }
  var ans := if countEven == 1 then idxEven + 1 else idxOdd + 1;
  output := IntToString(ans);
}

