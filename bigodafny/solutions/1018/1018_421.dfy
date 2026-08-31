// 1351_B. Square?  (problem 1018, solution 1018_421)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #By maxwill, contest: Testing Round #16 (Unrated), problem: (B) Square?, Compilation error, #, Copy
// T = int(input().strip())
// for i in range(T):
//     a = list(map(int, input().strip().split()))
//     b = list(map(int, input().strip().split()))
//     flag = False
//     for i in range(2):
//         for j in range(2):
//             if(a[i] == b[j] and a[1-i]+b[1-j] == a[i]):
//                 flag = True
//     
//     print("Yes" if flag else "No" ) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
