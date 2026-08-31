// p03523 CODE FESTIVAL 2017 Final - AKIBA  (problem 831, solution 831_184)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// S = list(input())
// T = list("AKIHABARA")
// ans = "YES"
// i = 0
// while i < len(S) and i < 9:
//     if S[i] != T[i]:
//         if T[i] == "A":
//             S.insert(i,"A")
//     i += 1
// if S[-1] != "A":
//     S += "A"
// 
// if S == T:
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(word: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
