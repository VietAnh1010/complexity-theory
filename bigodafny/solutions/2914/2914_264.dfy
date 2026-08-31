// 1136_A. Nastya Is Reading a Book  (problem 2914, solution 2914_264)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// mas =  []
// 
// for i in range(n):
//     c = list(map(int,input().split()))
//     mas.append(c)
// 
// k = int(input())
// 
// for i in range(n):
//     if k >= mas[i][0] and k <= mas[i][1]:
//         print(n-i)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, intervals: seq<seq<int>>, value: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
