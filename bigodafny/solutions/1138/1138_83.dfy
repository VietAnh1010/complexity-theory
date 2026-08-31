// 499_A. Watching a movie  (problem 1138, solution 1138_83)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x = map(int, input().split())
// data = []
// result = 0
// 
// for _ in range(n):
//     data.append(list(map(int, input().split())))
// 
// for i in range(n):
//     if i==0:
//         result += (data[i][0]-1)%x
//     else:
//         result += (data[i][0]-data[i-1][1]-1)%x
//     result += data[i][1]-data[i][0]+1
// 
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, data: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
