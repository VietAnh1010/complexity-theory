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
  output := ""; // TODO: translate the Python above
}
