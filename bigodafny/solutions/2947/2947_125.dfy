// 637_A. Voting for Photos  (problem 2947, solution 2947_125)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(x) for x in input().split()]
// score = dict()
// sup, winner = -2**31, None
// for v in a:
//     score[v] = score[v] + 1 if v in score else 1
//     if score[v] > sup:
//         sup, winner = score[v], v
// print(winner)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
