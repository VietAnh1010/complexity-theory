// 454_B. Little Pony and Sort by Shift  (problem 71, solution 71_257)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #Codeforces454B
// n = int(input())
// lst = [int(x) for x in input().split()]
// index = 0
// count = 0
// for i in range(n):
//     
//     if lst[i-1] > lst[i]:
//         index = i
//         count += 1
//     if count == 2:
//         print(-1)
//         break
// 
// if count != 2:
//     print((n - index) % n)
//  
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
