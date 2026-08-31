// 1105_B. Zuhair and Strings  (problem 2231, solution 2231_77)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// k = int(input().split()[1])
// result = {}
// prev = 0
// value = 0
// STR = input() + '$'
// 
// for letter in STR:
//     if letter != prev:
//         result[prev] = result.get(prev, 0) + value//k
//         prev = letter
//         value = 0
//     value+=1
// 
// print(max(result.values()))  
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, string_: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
