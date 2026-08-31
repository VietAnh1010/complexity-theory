// 768_A. Oath of the Night's Watch  (problem 1997, solution 1997_311)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// stewards = sorted(list(map(int, input().split())))
// help = 0
// mx = max(stewards)
// mn = min(stewards)
// 
// for each in stewards:
//     if mn < each < mx:
//         help += 1
// 
// print(help)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
