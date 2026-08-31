// 879_A. Borya's Diagnosis  (problem 827, solution 827_148)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = [[0,0] for i in range(n)]
// 
// for i in range(n):
//     arr[i][0] , arr[i][1] = map(int , input().split())
// 
// # arr.sort(key = lambda x: x[1])
// dates = [arr[0][0]]
// 
// for i,j in arr[1:]:
//     while i<=dates[-1] : i += j
//     dates.append(i)
// 
// 
// print(dates[-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
