// 462_A. Appleman and Easy Task  (problem 1345, solution 1345_113)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def giveResponse(mat,n):
//     for i in range(1,n+1):
//         for j in range(1,n+1):
//             if (mat[i-1][j] + mat[i+1][j] + mat[i][j-1] + mat[i][j+1])%2==1:
//                 return("NO")
//     return("YES")
// 
// mat=[]
// n = int(input())
// mat = [[0]*(n+2)]
// for i in range(n):
//     sat = [0]
//     for j in (input()):
//         if j=='o':
//             sat.append(1)
//         else:
//             sat.append(0)
//     sat.append(0)
//     mat.append(sat)
// mat.append( [0]*(n+2))
// 
// print(giveResponse(mat,n))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, board: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
